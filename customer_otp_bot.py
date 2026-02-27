import os
import json
import re
import asyncio
import logging
import time
import threading
from typing import Optional
from datetime import datetime
from pathlib import Path

import httpx
from bs4 import BeautifulSoup
from telegram import Update
from telegram.ext import Application, CommandHandler, ContextTypes

from telegram.request import HTTPXRequest
from telegram.error import Forbidden, RetryAfter, BadRequest, TimedOut, NetworkError

import redis.asyncio as redis

logging.basicConfig(
    format="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
    level=logging.INFO,
)
logger = logging.getLogger(__name__)

# ----------- ENV -----------
TG_TOKEN = os.getenv("TG_TOKEN")
ADMIN_IDS = [int(x.strip()) for x in os.getenv("ADMIN_IDS", "6356573938").split(",")]

ALLOWED_DOMAIN = [
    d.strip().lower()
    for d in os.getenv("ALLOWED_DOMAIN", "").split(",")
    if d.strip()
]

MAX_REQUESTS_PER_USER = int(os.getenv("MAX_REQUESTS_PER_USER", "10"))
DELAY_SECONDS = int(os.getenv("DELAY_SECONDS", "30"))
STATE_FILE = os.getenv("STATE_FILE", "state.json")
COOLDOWN_SECONDS = 91  # ~3 minutes cooldown after success OR "no OTP"

# Special domain(s) where limit applies per EMAIL instead of Telegram ID
EMAIL_QUOTA_DOMAINS = [
    d.strip().lower()
    for d in os.getenv("EMAIL_QUOTA_DOMAINS", "").split(",")
    if d.strip()
]
EMAIL_QUOTA_LIMIT = int(os.getenv("EMAIL_QUOTA_LIMIT", "10"))

# ✅ NEW: Require users to be member of this channel/group to use bot
# Example: REQUIRED_CHAT_ID=@mychannel  OR  REQUIRED_CHAT_ID=-1001234567890
REQUIRED_CHAT_ID = os.getenv("REQUIRED_CHAT_ID", "").strip()

# Redis URL for shared watchlist storage
REDIS_URL = os.getenv("REDIS_URL", "").strip()

RESTART_EVERY_MIN = int(os.getenv("RESTART_EVERY_MIN", "0"))  # 0 = disabled
ERROR_RESTART_THRESHOLD = int(os.getenv("ERROR_RESTART_THRESHOLD", "6"))
# ---------------------------

OTP_PATTERN = re.compile(r"\b(\d{6})\b")

WATCHLIST_KEY = "warn:watchlist"
INTERVAL_KEY = "warn:interval_min"

_CONSEC_ERRORS = 0


def _allowed_domains_text() -> str:
    return ", ".join(f"@{d}" for d in ALLOWED_DOMAIN)


def _is_allowed_domain(email: str) -> bool:
    return any(email.endswith(f"@{d}") for d in ALLOWED_DOMAIN)


def _parse_ids(text: str):
    return [int(x) for x in re.findall(r"\d+", text or "")]


def _email_domain(email: str) -> str:
    if "@" not in email:
        return ""
    return email.split("@", 1)[1].strip().lower()


def _is_email_quota_domain(email: str) -> bool:
    d = _email_domain(email)
    return d in EMAIL_QUOTA_DOMAINS if d else False


def _required_chat_display() -> str:
    if not REQUIRED_CHAT_ID:
        return ""
    return REQUIRED_CHAT_ID


async def require_membership(update: Update, context: ContextTypes.DEFAULT_TYPE) -> bool:
    """
    Returns True if user is allowed (member/admin/creator) OR if REQUIRED_CHAT_ID not set OR if admin bypass.
    Returns False and sends a message if user is not a member.
    """
    if not update.effective_user:
        return False

    user_id = update.effective_user.id

    # Admin bypass (optional)
    if user_id in ADMIN_IDS:
        return True

    # If not configured, do nothing
    if not REQUIRED_CHAT_ID:
        return True

    try:
        member = await context.bot.get_chat_member(chat_id=REQUIRED_CHAT_ID, user_id=user_id)
        status = getattr(member, "status", "")
        # allowed statuses
        if status in ("member", "administrator", "creator"):
            return True

        # Not a member / left / kicked / restricted
        if update.message:
            await update.message.reply_text(
                f"⛔ You must join our channel to use this bot.\n\n"
                f"✅ Join: {_required_chat_display()}\n"
                f"Then try again."
            )
        return False

    except Forbidden:
        # Bot not allowed to see members (usually bot not admin in channel)
        if update.message:
            await update.message.reply_text(
                "⚠️ Bot cannot verify your channel membership right now.\n"
                "Admin needs to add the bot as an admin in the required channel."
            )
        return False
    except BadRequest as e:
        # wrong chat id or private channel etc.
        if update.message:
            await update.message.reply_text(
                f"⚠️ Membership check failed (bad chat id).\n"
                f"Please contact admin.\n\nError: {e}"
            )
        return False
    except Exception as e:
        logger.error(f"Membership check error: {e}")
        if update.message:
            await update.message.reply_text("⚠️ Could not verify membership. Please try again later.")
        return False


redis_client = redis.from_url(REDIS_URL, decode_responses=True) if REDIS_URL else None


class StateManager:
    def __init__(self, state_file: str):
        self.state_file = state_file
        self.state = self._load_state()

    def _load_state(self) -> dict:
        Path(self.state_file).parent.mkdir(parents=True, exist_ok=True)
        if os.path.exists(self.state_file):
            try:
                with open(self.state_file, "r") as f:
                    data = json.load(f)
            except Exception as e:
                logger.error(f"Error loading state: {e}")
                data = {}
        else:
            data = {}

        data.setdefault("user_requests", {})
        data.setdefault("email_requests", {})
        data.setdefault("cached_otps", {})
        data.setdefault("cooldowns", {})
        data.setdefault("blocked_emails", {})
        data.setdefault("subscribers", [])
        return data

    def _save_state(self):
        try:
            with open(self.state_file, "w") as f:
                json.dump(self.state, f, indent=2)
        except Exception as e:
            logger.error(f"Error saving state: {e}")

    def get_user_requests(self, user_id: int) -> int:
        return self.state["user_requests"].get(str(user_id), 0)

    def increment_user_requests(self, user_id: int):
        uid = str(user_id)
        self.state["user_requests"][uid] = self.state["user_requests"].get(uid, 0) + 1
        self._save_state()

    def reset_user_limit(self, user_id: int):
        uid = str(user_id)
        if uid in self.state["user_requests"]:
            del self.state["user_requests"][uid]
        self._save_state()

    def get_email_requests(self, email: str) -> int:
        email = (email or "").strip().lower()
        return self.state["email_requests"].get(email, 0)

    def increment_email_requests(self, email: str):
        email = (email or "").strip().lower()
        self.state["email_requests"][email] = self.state["email_requests"].get(email, 0) + 1
        self._save_state()

    def cache_otp(self, email: str, otp: str):
        self.state["cached_otps"][email] = {
            "otp": otp,
            "timestamp": datetime.now().isoformat(),
        }
        self._save_state()

    def clear_email(self, email: str):
        if email in self.state["cached_otps"]:
            del self.state["cached_otps"][email]
            self._save_state()
            return True
        return False

    def set_cooldown(self, user_id: int, seconds: int):
        next_allowed = int(time.time()) + seconds
        self.state["cooldowns"][str(user_id)] = next_allowed
        self._save_state()

    def remaining_cooldown(self, user_id: int) -> int:
        now = int(time.time())
        next_allowed = int(self.state["cooldowns"].get(str(user_id), 0))
        if next_allowed > now:
            return next_allowed - now
        return 0

    def is_blocked(self, email: str) -> bool:
        return email in self.state.get("blocked_emails", {})

    def block_email(self, email: str, by_user_id: int):
        self.state["blocked_emails"][email] = {
            "timestamp": datetime.now().isoformat(),
            "by": by_user_id,
        }
        self._save_state()

    def unblock_email(self, email: str) -> bool:
        if email in self.state.get("blocked_emails", {}):
            del self.state.get("blocked_emails", {})[email]
            self._save_state()
            return True
        return False

    def add_subscriber(self, chat_id: int):
        cid = int(chat_id)
        if cid not in self.state["subscribers"]:
            self.state["subscribers"].append(cid)
            self._save_state()

    def get_subscribers(self):
        return list(self.state.get("subscribers", []))

    def remove_subscriber(self, chat_id: int) -> bool:
        cid = int(chat_id)
        if cid in self.state.get("subscribers", []):
            self.state["subscribers"].remove(cid)
            self._save_state()
            return True
        return False


state_manager = StateManager(STATE_FILE)


async def fetch_otp_from_generator(email: str) -> Optional[str]:
    inbox_url = f"https://generator.email/{email}"

    headers = {
        "User-Agent": (
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
            "AppleWebKit/537.36 (KHTML, like Gecko) "
            "Chrome/120.0.0.0 Safari/537.36"
        ),
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,*/*;q=0.8",
        "Accept-Language": "en-US,en;q=0.5",
        "Accept-Encoding": "gzip, deflate, br",
        "Connection": "keep-alive",
        "Upgrade-Insecure-Requests": "1",
        "Sec-Fetch-Dest": "document",
        "Sec-Fetch-Mode": "navigate",
        "Sec-Fetch-Site": "none",
        "Cache-Control": "max-age=0",
        "Referer": "https://generator.email/",
    }

    max_retries = 3

    async with httpx.AsyncClient(timeout=httpx.Timeout(25.0), follow_redirects=True) as client:
        for attempt in range(max_retries):
            try:
                logger.info(f"Fetching {inbox_url} (attempt {attempt + 1}/{max_retries})")
                response = await client.get(inbox_url, headers=headers)
                response.raise_for_status()

                soup = BeautifulSoup(response.text, "html.parser")

                newest_link = None
                email_table = soup.find(id="email-table")
                if email_table:
                    first_a = email_table.find("a", href=True)
                    if first_a and first_a.get("href"):
                        newest_link = first_a["href"].strip()

                if newest_link:
                    if newest_link.startswith("/"):
                        newest_url = "https://generator.email" + newest_link
                    elif newest_link.startswith("http"):
                        newest_url = newest_link
                    else:
                        newest_url = "https://generator.email/" + newest_link

                    msg_resp = await client.get(newest_url, headers={**headers, "Referer": inbox_url})
                    msg_resp.raise_for_status()
                    msg_soup = BeautifulSoup(msg_resp.text, "html.parser")

                    msg_text = msg_soup.get_text(" ", strip=True)
                    msg_matches = OTP_PATTERN.findall(msg_text)
                    if msg_matches:
                        return msg_matches[0]

                    iframe = msg_soup.find("iframe", src=True)
                    if iframe and iframe.get("src"):
                        iframe_src = iframe["src"].strip()
                        if iframe_src.startswith("/"):
                            iframe_url = "https://generator.email" + iframe_src
                        elif iframe_src.startswith("http"):
                            iframe_url = iframe_src
                        else:
                            iframe_url = "https://generator.email/" + iframe_src

                        iframe_resp = await client.get(iframe_url, headers={**headers, "Referer": newest_url})
                        iframe_resp.raise_for_status()
                        iframe_text = BeautifulSoup(iframe_resp.text, "html.parser").get_text(" ", strip=True)
                        iframe_matches = OTP_PATTERN.findall(iframe_text)
                        if iframe_matches:
                            return iframe_matches[0]

                email_bodies = soup.find_all(["div", "p", "span", "td"])
                for element in email_bodies:
                    text = element.get_text()
                    matches = OTP_PATTERN.findall(text)
                    if matches:
                        return matches[0]

                return None

            except httpx.HTTPError as e:
                logger.error(f"Request error (attempt {attempt + 1}): {e}")
                if attempt < max_retries - 1:
                    await asyncio.sleep(2)
                else:
                    raise

    return None


def _start_timed_restart_thread():
    if RESTART_EVERY_MIN <= 0:
        return

    def _worker():
        logger.warning(f"Timed restart enabled. Will restart every {RESTART_EVERY_MIN} minutes.")
        while True:
            time.sleep(RESTART_EVERY_MIN * 60)
            logger.warning("Restarting bot now...")
            import sys
            os.execv(sys.executable, ["python"] + sys.argv)

    t = threading.Thread(target=_worker, daemon=True)
    t.start()


def _note_net_success():
    global _CONSEC_ERRORS
    _CONSEC_ERRORS = 0


def _note_net_error_and_maybe_restart():
    global _CONSEC_ERRORS
    _CONSEC_ERRORS += 1
    if ERROR_RESTART_THRESHOLD > 0 and _CONSEC_ERRORS >= ERROR_RESTART_THRESHOLD:
        logger.error(
            f"Consecutive network errors reached {ERROR_RESTART_THRESHOLD}. "
            "Exiting for Railway to auto-restart."
        )
        os._exit(1)


# ---------------- Commands ----------------
async def start_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not update.message:
        return

    if update.effective_chat:
        state_manager.add_subscriber(update.effective_chat.id)

    domains_text = _allowed_domains_text()

    join_text = ""
    if REQUIRED_CHAT_ID:
        join_text = f"\n🔒 Requirement: You must join {_required_chat_display()} to use this bot.\n"

    await update.message.reply_text(
        "✨ Welcome to Digital Creed OTP Service ✨\n\n"
        "📌 HOW TO USE:\n"
        "👉 /otp username@domain.com\n\n"
        "📩 Examples:\n"
        "• /otp dcreedprivate.kaviska@eliotkids.com\n"
        "• /otp dcplus.ajanthan41@kabarr.com\n\n"
        f"✅ Allowed domains: {domains_text}\n"
        f"⏱️ Wait: {DELAY_SECONDS} seconds before checking.\n"
        f"👤 Limit: {MAX_REQUESTS_PER_USER} successful OTPs per Telegram user (default).\n"
        + join_text
    )


async def otp_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not update.message:
        return

    # ✅ membership gate
    ok = await require_membership(update, context)
    if not ok:
        return

    user = update.effective_user
    if not user:
        return

    if update.effective_chat:
        state_manager.add_subscriber(update.effective_chat.id)

    is_admin = user.id in ADMIN_IDS

    if not is_admin:
        cd = state_manager.remaining_cooldown(user.id)
        if cd > 0:
            await update.message.reply_text(f"⏳ Please wait {cd} seconds before requesting again.")
            return

    if not context.args:
        await update.message.reply_text(
            "❌ Please provide an email address.\n\n"
            "Use:\n"
            "/otp username@domain.com"
        )
        return

    email = context.args[0].strip().lower()

    if not _is_allowed_domain(email):
        await update.message.reply_text(f"❌ Invalid email domain. Only {_allowed_domains_text()} is supported.")
        return

    use_email_quota = (not is_admin) and _is_email_quota_domain(email)

    if state_manager.is_blocked(email):
        if not is_admin:
            state_manager.set_cooldown(user.id, COOLDOWN_SECONDS)
        await update.message.reply_text("❌ No OTP found right now. Please try again later.")
        return

    if not is_admin:
        if use_email_quota:
            current_requests = state_manager.get_email_requests(email)
            if current_requests >= EMAIL_QUOTA_LIMIT:
                await update.message.reply_text(f"⛔ This email reached its limit ({EMAIL_QUOTA_LIMIT}).")
                return
            remaining_if_success = EMAIL_QUOTA_LIMIT - (current_requests + 1)
        else:
            current_requests = state_manager.get_user_requests(user.id)
            if current_requests >= MAX_REQUESTS_PER_USER:
                await update.message.reply_text(f"⛔ You reached your limit ({MAX_REQUESTS_PER_USER}).")
                return
            remaining_if_success = MAX_REQUESTS_PER_USER - (current_requests + 1)
    else:
        remaining_if_success = "∞"

    await update.message.reply_text(
        f"⏳ Waiting {DELAY_SECONDS} seconds before checking…\n"
        f"📧 {email}\n"
        f"📊 Remaining (if success): {remaining_if_success}"
        + (f"\n🎯 Mode: PER EMAIL ({EMAIL_QUOTA_LIMIT})" if use_email_quota else "")
    )

    if not is_admin:
        await asyncio.sleep(DELAY_SECONDS)

    max_rounds = 5
    for round_idx in range(1, max_rounds + 1):
        try:
            otp = await fetch_otp_from_generator(email)

            if otp:
                if not is_admin:
                    if use_email_quota:
                        state_manager.increment_email_requests(email)
                    else:
                        state_manager.increment_user_requests(user.id)

                state_manager.cache_otp(email, otp)

                if not is_admin:
                    state_manager.set_cooldown(user.id, COOLDOWN_SECONDS)

                _note_net_success()

                if not is_admin:
                    if use_email_quota:
                        now_used = state_manager.get_email_requests(email)
                        remaining = EMAIL_QUOTA_LIMIT - now_used
                    else:
                        now_used = state_manager.get_user_requests(user.id)
                        remaining = MAX_REQUESTS_PER_USER - now_used
                else:
                    remaining = "∞"

                await update.message.reply_text(
                    f"✅ OTP Found!\n\n"
                    f"🔢 Code: `{otp}`\n"
                    f"📧 {email}\n"
                    f"📊 Remaining: {remaining}"
                    + (f"\n🎯 Mode: PER EMAIL ({EMAIL_QUOTA_LIMIT})" if use_email_quota else ""),
                    parse_mode="Markdown",
                )
                return

            else:
                if not is_admin:
                    state_manager.set_cooldown(user.id, COOLDOWN_SECONDS)
                _note_net_success()
                await update.message.reply_text("❌ No OTP found right now. Please try again later.")
                return

        except httpx.HTTPError:
            if round_idx < max_rounds:
                await update.message.reply_text(
                    f"⚠️ Network issue (attempt {round_idx}/{max_rounds}). Retrying in 5 seconds..."
                )
                await asyncio.sleep(5)
                continue

            _note_net_error_and_maybe_restart()
            await update.message.reply_text("⚠️ Network issue. Please wait a few minutes and try again.")
            return

        except Exception as e:
            logger.error(f"Unexpected error in otp_command: {e}")
            _note_net_error_and_maybe_restart()
            await update.message.reply_text("❌ An unexpected error occurred. Please try again.")
            return


async def remaining_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not update.message:
        return

    # ✅ membership gate
    ok = await require_membership(update, context)
    if not ok:
        return

    user = update.effective_user
    if not user:
        return

    current_requests = state_manager.get_user_requests(user.id)
    cd = state_manager.remaining_cooldown(user.id)

    if cd > 0:
        text = f"📊 Used: {current_requests}/{MAX_REQUESTS_PER_USER}\n⏱️ Cooldown: {cd} seconds left"
    else:
        text = f"📊 Used: {current_requests}/{MAX_REQUESTS_PER_USER}\n✅ No cooldown active"

    await update.message.reply_text(text)


async def error_handler(update: object, context: ContextTypes.DEFAULT_TYPE):
    logger.error(f"Update {update} caused error {context.error}")


def _build_application() -> Application:
    tg_request = HTTPXRequest(
        connect_timeout=30,
        read_timeout=30,
        write_timeout=30,
        pool_timeout=30,
    )

    app = (
        Application.builder()
        .token(TG_TOKEN)
        .request(tg_request)
        .concurrent_updates(True)
        .build()
    )

    app.add_handler(CommandHandler("start", start_command))
    app.add_handler(CommandHandler("otp", otp_command))
    app.add_handler(CommandHandler("remaining", remaining_command))

    app.add_error_handler(error_handler)
    return app


def main():
    if not TG_TOKEN:
        logger.error("TG_TOKEN environment variable is not set!")
        print("❌ ERROR: TG_TOKEN environment variable is required.")
        return

    if not ALLOWED_DOMAIN:
        logger.error("ALLOWED_DOMAIN environment variable is not set or empty!")
        print("❌ ERROR: ALLOWED_DOMAIN environment variable is required (comma-separated if multiple).")
        return

    logger.info("Starting OTP bot...")
    _start_timed_restart_thread()

    backoff = 2
    while True:
        try:
            application = _build_application()
            application.run_polling(allowed_updates=Update.ALL_TYPES)
            backoff = 2
        except (TimedOut, NetworkError, httpx.HTTPError, OSError) as e:
            logger.error(f"Telegram/network startup error: {e} — retrying in {backoff}s")
            time.sleep(backoff)
            backoff = min(backoff * 2, 60)
            continue
        except Exception as e:
            logger.exception(f"Fatal unexpected error: {e}")
            _note_net_error_and_maybe_restart()
            time.sleep(5)


if __name__ == "__main__":
    main()
