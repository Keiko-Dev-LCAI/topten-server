#!/usr/bin/env python3
"""
Top Ten — Daily AI Presale Analysis
Powered by Lightchain AIVM
Fetches top 10 active crypto presales, runs AIVM analysis, caches results.
Runs once per day at 6 AM Eastern via APScheduler.
"""

import json
import os
import re
import secrets
import base64
import threading
import time
from datetime import datetime, timezone

import requests
from flask import Flask, jsonify, request
from apscheduler.schedulers.background import BackgroundScheduler
import pytz

# ════════════════════════════════════════════════════════════════════════
# CONSTANTS
# ════════════════════════════════════════════════════════════════════════

CACHE_FILE = "/tmp/presales_cache.json"
CACHE_MAX_AGE_HOURS = 25

AIVM_GATEWAY  = "https://chat-api.mainnet.lightchain.ai"
AIVM_RELAY    = "wss://relay.mainnet.lightchain.ai/ws"
AIVM_RPC      = "https://rpc.mainnet.lightchain.ai"
AIVM_JOB_REG  = "0xfB15F90298e4CcD7106E76fFB5e520315cC42B0b"
AIVM_JOB_FEE  = 20_000_000_000_000_000   # 0.02 LCAI in wei
AIVM_CHAIN_ID = 9200

AIVM_ABI = [
    {
        "name": "createSession", "type": "function", "stateMutability": "payable",
        "inputs": [
            {"name": "paramsHash",     "type": "bytes32"},
            {"name": "worker",         "type": "address"},
            {"name": "encWorkerKey",   "type": "bytes"},
            {"name": "ephemeralPubKey","type": "bytes"},
            {"name": "initState",      "type": "bytes"},
            {"name": "expiry",         "type": "uint256"},
        ],
        "outputs": [{"name": "sessionId", "type": "uint256"}],
    },
    {
        "name": "submitJob", "type": "function", "stateMutability": "payable",
        "inputs": [
            {"name": "sessionId",  "type": "uint256"},
            {"name": "promptHash", "type": "bytes32"},
        ],
        "outputs": [{"name": "jobId", "type": "uint256"}],
    },
    {
        "anonymous": False, "name": "SessionCreated", "type": "event",
        "inputs": [
            {"indexed": True,  "name": "sessionId",     "type": "uint256"},
            {"indexed": True,  "name": "user",           "type": "address"},
            {"indexed": True,  "name": "paramsHash",     "type": "bytes32"},
            {"indexed": False, "name": "worker",         "type": "address"},
            {"indexed": False, "name": "encWorkerKey",   "type": "bytes"},
            {"indexed": False, "name": "ephemeralPubKey","type": "bytes"},
        ],
    },
    {
        "anonymous": False, "name": "JobSubmitted", "type": "event",
        "inputs": [
            {"indexed": True,  "name": "jobId",     "type": "uint256"},
            {"indexed": True,  "name": "sessionId", "type": "uint256"},
            {"indexed": False, "name": "worker",    "type": "address"},
        ],
    },
    {
        "anonymous": False, "name": "JobCompleted", "type": "event",
        "inputs": [
            {"indexed": True,  "name": "jobId",          "type": "uint256"},
            {"indexed": True,  "name": "worker",          "type": "address"},
            {"indexed": False, "name": "responseHash",    "type": "bytes32"},
            {"indexed": False, "name": "ciphertextHash",  "type": "bytes32"},
        ],
    },
]


# ════════════════════════════════════════════════════════════════════════
# AIVM HELPER FUNCTIONS (verbatim from OrcaGuard)
# ════════════════════════════════════════════════════════════════════════

def _decode_pubkey(s):
    """Accept hex (with/without 0x) or base64; return 65-byte uncompressed P-256 point."""
    if isinstance(s, (bytes, bytearray)):
        return bytes(s)
    s = s.strip()
    if s.startswith('0x') or s.startswith('0X'):
        b = bytes.fromhex(s[2:])
    elif len(s) == 130 and all(c in '0123456789abcdefABCDEF' for c in s):
        b = bytes.fromhex(s)
    else:
        b = base64.b64decode(s)
    if len(b) != 65:
        raise ValueError(f"pubkey decode: expected 65 bytes, got {len(b)}")
    return b


def _ecdh_wrap(session_key: bytes, peer_pub_bytes: bytes) -> bytes:
    """ECDH-wrap session_key for peer P-256 pubkey."""
    from cryptography.hazmat.primitives.asymmetric.ec import (
        generate_private_key, ECDH, EllipticCurvePublicNumbers, SECP256R1
    )
    from cryptography.hazmat.primitives.ciphers.aead import AESGCM
    from cryptography.hazmat.backends import default_backend

    x = int.from_bytes(peer_pub_bytes[1:33], 'big')
    y = int.from_bytes(peer_pub_bytes[33:65], 'big')
    peer_pub = EllipticCurvePublicNumbers(x, y, SECP256R1()).public_key(default_backend())

    ephem_priv = generate_private_key(SECP256R1(), default_backend())
    shared = ephem_priv.exchange(ECDH(), peer_pub)

    pub_nums = ephem_priv.public_key().public_numbers()
    ephem_pub_bytes = (b'\x04' +
                       pub_nums.x.to_bytes(32, 'big') +
                       pub_nums.y.to_bytes(32, 'big'))

    nonce  = secrets.token_bytes(12)
    ct_tag = AESGCM(shared).encrypt(nonce, session_key, None)
    return ephem_pub_bytes + nonce + ct_tag


def _aes_encrypt(key: bytes, plaintext: bytes) -> bytes:
    """AES-256-GCM encrypt. Returns nonce(12) || ct || tag(16)."""
    from cryptography.hazmat.primitives.ciphers.aead import AESGCM
    nonce = secrets.token_bytes(12)
    return nonce + AESGCM(key).encrypt(nonce, plaintext, None)


def _aes_decrypt(key: bytes, blob: bytes) -> bytes:
    """AES-256-GCM decrypt nonce(12) || ct || tag(16)."""
    from cryptography.hazmat.primitives.ciphers.aead import AESGCM
    if len(blob) < 28:
        raise ValueError("ciphertext too short")
    return AESGCM(key).decrypt(blob[:12], blob[12:], None)


# ════════════════════════════════════════════════════════════════════════
# AIVM CLIENT (verbatim from OrcaGuard, adapted for chat interface)
# ════════════════════════════════════════════════════════════════════════

class AIVMClient:
    """Runs LLM inference through the Lightchain v2 decentralized worker network."""

    def __init__(self, private_key: str):
        from web3 import Web3
        from eth_account import Account

        self._req      = requests
        self._w3       = Web3(Web3.HTTPProvider(AIVM_RPC))
        self._account  = Account.from_key(private_key)
        self._registry = self._w3.eth.contract(
            address=Web3.to_checksum_address(AIVM_JOB_REG),
            abi=AIVM_ABI,
        )
        self._jwt     = None
        self._jwt_exp = 0
        print(f"  [AIVM] wallet: {self._account.address}")

    def _get_jwt(self) -> str:
        from eth_account.messages import encode_defunct
        if self._jwt and time.time() < self._jwt_exp - 30:
            return self._jwt
        r = self._req.get(
            f"{AIVM_GATEWAY}/api/auth/challenge",
            params={"address": self._account.address}, timeout=15,
        )
        r.raise_for_status()
        message = r.json()["message"]
        sig = self._account.sign_message(encode_defunct(text=message))
        r2 = self._req.post(
            f"{AIVM_GATEWAY}/api/auth/verify",
            json={"message": message, "signature": "0x" + sig.signature.hex()},
            timeout=15,
        )
        r2.raise_for_status()
        v = r2.json()
        self._jwt = v["token"]
        exp_str = v["expiresAt"][:19].replace("T", " ")
        self._jwt_exp = time.mktime(time.strptime(exp_str, "%Y-%m-%d %H:%M:%S"))
        return self._jwt

    def _auth_headers(self):
        return {
            "Authorization": f"Bearer {self._get_jwt()}",
            "Accept":        "application/json",
            "Content-Type":  "application/json",
        }

    def run_inference(self, full_prompt: str, timeout_secs: int = 360) -> str:
        import websocket as _ws
        from urllib.parse import quote as url_quote
        from web3 import Web3

        req = self._req
        print(f"  [AIVM] starting inference ({len(full_prompt)} chars)")

        # 1-2. Auth + pick model
        r = req.get(f"{AIVM_GATEWAY}/api/models", timeout=15)
        r.raise_for_status()
        models = r.json().get("models", [])
        model  = next((m for m in models if m["name"] == "llama3-8b"), models[0] if models else None)
        if not model:
            raise RuntimeError("No models available from AIVM gateway")
        model_id = model["id"]
        print(f"  [AIVM] model: {model['name']} id={model_id[:10]}...")

        # 3. Select worker
        r = req.post(
            f"{AIVM_GATEWAY}/api/sessions/select",
            json={"modelId": model_id},
            headers=self._auth_headers(), timeout=15,
        )
        r.raise_for_status()
        sel = r.json()
        print(f"  [AIVM] worker: {sel['worker']}")

        # 4-5. Session key + ECDH wrap
        session_key  = secrets.token_bytes(32)
        enc_worker   = _ecdh_wrap(session_key, _decode_pubkey(sel["workerEncryptionKey"]))
        enc_disputer = _ecdh_wrap(session_key, _decode_pubkey(sel["disputerEncryptionKey"]))

        # 6. Prepare (get dispatcher signature)
        r = req.post(
            f"{AIVM_GATEWAY}/api/sessions/prepare",
            json={
                "modelId":        model_id,
                "encWorkerKey":   base64.b64encode(enc_worker).decode(),
                "encDisputerKey": base64.b64encode(enc_disputer).decode(),
            },
            headers=self._auth_headers(), timeout=15,
        )
        r.raise_for_status()
        prep = r.json()

        # 7. createSession on-chain
        def _h(s): return s[2:] if isinstance(s, str) and s[:2].lower() == '0x' else s
        params_hash = bytes.fromhex(_h(model_id).zfill(64))
        sig_bytes   = bytes.fromhex(_h(prep["signature"]))
        gas_price = self._w3.eth.gas_price
        nonce_val = self._w3.eth.get_transaction_count(self._account.address)

        tx = self._registry.functions.createSession(
            params_hash,
            Web3.to_checksum_address(prep["worker"]),
            enc_worker,
            enc_disputer,
            sig_bytes,
            prep["expiry"],
        ).build_transaction({
            "from":     self._account.address,
            "nonce":    nonce_val,
            "gas":      1_000_000,
            "gasPrice": gas_price,
            "value":    0,
            "chainId":  AIVM_CHAIN_ID,
        })
        signed  = self._account.sign_transaction(tx)
        tx_hash = self._w3.eth.send_raw_transaction(signed.raw_transaction)
        print(f"  [AIVM] createSession tx: {tx_hash.hex()}")
        receipt1 = self._w3.eth.wait_for_transaction_receipt(tx_hash, timeout=90)
        if receipt1.status != 1:
            raise RuntimeError("createSession reverted on-chain")

        session_id = None
        for log in receipt1.logs:
            try:
                evt = self._registry.events.SessionCreated().process_log(log)
                session_id = evt["args"]["sessionId"]
                break
            except Exception:
                pass
        if session_id is None:
            raise RuntimeError("SessionCreated event not found in receipt")
        print(f"  [AIVM] sessionId: {session_id}")

        # 8. Get relay token
        relay_token = None
        deadline = time.time() + 120
        while time.time() < deadline:
            r = req.get(
                f"{AIVM_GATEWAY}/api/sessions/{session_id}/token",
                headers=self._auth_headers(), timeout=10,
            )
            if r.status_code == 200:
                d = r.json()
                if d.get("token"):
                    relay_token = d["token"]
                    break
            time.sleep(1)
        if not relay_token:
            raise RuntimeError("Relay token not ready within 120s")

        chunks   = []
        ws_ready = threading.Event()
        ws_err   = [None]

        def _on_message(ws_obj, message):
            try:
                frame = json.loads(message)
                payload = frame.get("payload")
                if not payload:
                    return
                blob = base64.b64decode(payload)
                try:
                    pt = _aes_decrypt(session_key, blob)
                    chunks.append(pt.decode("utf-8", errors="replace"))
                except Exception:
                    pass
            except Exception:
                pass

        def _on_open(ws_obj):
            ws_ready.set()

        def _on_error(ws_obj, err):
            ws_err[0] = err
            ws_ready.set()

        ws = _ws.WebSocketApp(
            f"{AIVM_RELAY}?token={url_quote(relay_token)}",
            on_message=_on_message,
            on_open=_on_open,
            on_error=_on_error,
        )
        ws_thread = threading.Thread(target=ws.run_forever, daemon=True)
        ws_thread.start()
        ws_ready.wait(timeout=15)
        if ws_err[0]:
            raise RuntimeError(f"WebSocket failed: {ws_err[0]}")
        print("  [AIVM] relay connected")

        # 9. Encrypt prompt + upload blob
        cipher = _aes_encrypt(session_key, full_prompt.encode("utf-8"))
        r = req.post(
            f"{AIVM_GATEWAY}/api/blobs",
            json={"data": base64.b64encode(cipher).decode()},
            headers=self._auth_headers(), timeout=15,
        )
        r.raise_for_status()
        blob_hashes = r.json().get("blobHashes", [])
        if not blob_hashes:
            raise RuntimeError("No blob hash returned from gateway")
        prompt_hash = bytes.fromhex(_h(blob_hashes[0]).zfill(64))

        # 10. submitJob (pay 0.02 LCAI)
        nonce_val2 = self._w3.eth.get_transaction_count(self._account.address)
        tx2 = self._registry.functions.submitJob(
            session_id,
            prompt_hash,
        ).build_transaction({
            "from":     self._account.address,
            "nonce":    nonce_val2,
            "gas":      500_000,
            "gasPrice": gas_price,
            "value":    AIVM_JOB_FEE,
            "chainId":  AIVM_CHAIN_ID,
        })
        signed2  = self._account.sign_transaction(tx2)
        tx_hash2 = self._w3.eth.send_raw_transaction(signed2.raw_transaction)
        print(f"  [AIVM] submitJob tx: {tx_hash2.hex()}")
        receipt2 = self._w3.eth.wait_for_transaction_receipt(tx_hash2, timeout=90)
        if receipt2.status != 1:
            raise RuntimeError("submitJob reverted — check LCAI balance")

        job_id = None
        for log in receipt2.logs:
            try:
                evt = self._registry.events.JobSubmitted().process_log(log)
                job_id = evt["args"]["jobId"]
                break
            except Exception:
                pass
        if job_id is None:
            raise RuntimeError("JobSubmitted event not found in receipt")
        print(f"  [AIVM] jobId: {job_id}")

        # 11. Poll for JobCompleted
        job_completed_topic = "0x" + Web3.keccak(
            text="JobCompleted(uint256,address,bytes32,bytes32)"
        ).hex()
        job_id_topic = "0x" + hex(job_id)[2:].zfill(64)

        done     = False
        deadline = time.time() + timeout_secs
        while time.time() < deadline and not done:
            time.sleep(5)
            if chunks:
                print(f"  [AIVM] relay data arrived ({len(chunks)} chunks), returning early")
                done = True
                break
            try:
                head = self._w3.eth.block_number
                logs = self._w3.eth.get_logs({
                    "address":   Web3.to_checksum_address(AIVM_JOB_REG),
                    "fromBlock": receipt2.blockNumber,
                    "toBlock":   head,
                    "topics":    [job_completed_topic, job_id_topic],
                })
                if logs:
                    done = True
                    print(f"  [AIVM] JobCompleted on-chain!")
            except Exception as e:
                print(f"  [AIVM] log poll error (retrying): {e}")

        time.sleep(4)  # grace period for final relay frames
        ws.close()

        result = "".join(chunks)
        if result:
            print(f"  [AIVM] inference done, {len(result)} chars")
            return result

        if not done:
            raise RuntimeError(f"Timeout after {timeout_secs}s waiting for JobCompleted")

        return result or "Sorry, the AI completed the job but returned no response. Please try again."

    def chat(self, system_prompt: str, user_prompt: str, timeout_secs: int = 360) -> str:
        """Convenience wrapper: builds full prompt from system + user parts."""
        full_prompt = f"[SYSTEM]\n{system_prompt}\n\n[USER]\n{user_prompt}"
        return self.run_inference(full_prompt, timeout_secs=timeout_secs)


# ════════════════════════════════════════════════════════════════════════
# AIVM CLIENT SINGLETON
# ════════════════════════════════════════════════════════════════════════

_aivm_client = None
_aivm_lock   = threading.Lock()


def get_aivm_client():
    global _aivm_client
    with _aivm_lock:
        pk = os.environ.get("LIGHTCHAIN_PRIVATE_KEY", "").strip()
        if not pk:
            return None
        if _aivm_client is None:
            try:
                _aivm_client = AIVMClient(pk)
            except Exception as e:
                print(f"  [AIVM] init failed: {e}")
                return None
        return _aivm_client


# ════════════════════════════════════════════════════════════════════════
# PRESALE ANALYSIS PROMPTS
# ════════════════════════════════════════════════════════════════════════

CUSTOM_ANALYSIS_SYSTEM_PROMPT = """You are an expert crypto presale analyst with deep knowledge of tokenomics, rug pull patterns, and DeFi risk assessment. Perform a thorough deep-dive analysis of this presale.

Be specific and concrete. Identify exact red flags and green flags based on the data. Calculate implicit things: if presale rate is X and listing rate is Y, calculate the markup/dilution. If liquidity lock is only 30 days, flag it explicitly. If team tokens are >20%, flag it.

Return ONLY valid JSON, no markdown, no code blocks:
{
  "score": <1-10>,
  "verdict": "<one strong sentence overall verdict>",
  "green_flags": ["<specific flag with numbers/details>"],
  "red_flags": ["<specific flag with numbers/details>"],
  "analysis": "<3-4 sentence detailed breakdown covering tokenomics, team allocation, liquidity, and timing risks>",
  "recommendation": "BUY|WATCH|AVOID",
  "risk_breakdown": {
    "tokenomics": <1-10>,
    "team_transparency": <1-10>,
    "liquidity_safety": <1-10>,
    "timing_risk": <1-10>
  }
}"""

ANALYSIS_SYSTEM_PROMPT = """You are an expert crypto presale analyst. Analyze the presale data provided and return ONLY a valid JSON object. No markdown, no explanation, no code blocks — just raw JSON.

JSON format:
{
  "score": <integer 1-10>,
  "verdict": "<one sentence overall verdict>",
  "green_flags": ["<flag>", "<flag>", "<flag>"],
  "red_flags": ["<flag>", "<flag>"],
  "analysis": "<2-3 sentence detailed analysis>",
  "recommendation": "<BUY / WATCH / AVOID>"
}

Score guide: 8-10 = strong project, 5-7 = worth watching, 1-4 = high risk/avoid."""


def _default_analysis():
    return {
        "score": 5,
        "verdict": "Analysis unavailable — data could not be processed.",
        "green_flags": ["Listed on active presale platform"],
        "red_flags": ["Analysis incomplete — verify independently"],
        "analysis": "AIVM analysis was unavailable for this presale. Please research this project independently using multiple sources before making any investment decision.",
        "recommendation": "WATCH"
    }


def analyze_presale(presale_data: dict) -> dict:
    """Run AIVM analysis on a single presale. Returns analysis dict."""
    client = get_aivm_client()
    if not client:
        print("  [TopTen] AIVM unavailable — returning default analysis")
        return _default_analysis()

    user_prompt = json.dumps(presale_data, indent=2, default=str)
    try:
        raw = client.chat(ANALYSIS_SYSTEM_PROMPT, user_prompt, timeout_secs=120)
        # Strip any accidental markdown fences
        cleaned = re.sub(r"```(?:json)?", "", raw).strip().strip("`").strip()
        # Find first { to last }
        start = cleaned.find("{")
        end   = cleaned.rfind("}") + 1
        if start >= 0 and end > start:
            cleaned = cleaned[start:end]
        result = json.loads(cleaned)
        # Validate required keys
        for key in ("score", "verdict", "green_flags", "red_flags", "analysis", "recommendation"):
            if key not in result:
                raise ValueError(f"Missing key: {key}")
        result["score"] = max(1, min(10, int(result["score"])))
        return result
    except Exception as e:
        print(f"  [TopTen] analysis parse failed: {e} | raw: {raw[:200] if 'raw' in dir() else 'N/A'}")
        return _default_analysis()


# ════════════════════════════════════════════════════════════════════════
# CUSTOM ANALYSIS HELPERS
# ════════════════════════════════════════════════════════════════════════

def parse_input_type(user_input: str) -> dict:
    """Detect if input is a Pinksale URL, DxSale URL, contract address, or plain text."""
    s = user_input.strip()
    # Pinksale URL
    for pattern in [
        r'pinksale\.finance/(?:launchpad|presale)/([0-9a-fA-Fx]+)',
        r'pinksale\.finance/.*?([0-9a-fA-F]{40,})',
    ]:
        m = re.search(pattern, s, re.IGNORECASE)
        if m:
            return {"type": "pinksale", "id": m.group(1), "raw": s}
    # DxSale URL
    if "dxsale" in s.lower() or "dx.app" in s.lower():
        return {"type": "dxsale", "raw": s}
    # Contract address
    m = re.search(r'0x[0-9a-fA-F]{40}', s)
    if m:
        return {"type": "contract", "address": m.group(0), "raw": s}
    # Plain text
    return {"type": "text", "name": s, "raw": s}


def fetch_pinksale_details(launchpad_id: str) -> dict:
    """Fetch detailed launchpad data from Pinksale API."""
    try:
        resp = requests.get(
            f"https://api.pinksale.finance/api/v1/launchpad/{launchpad_id}",
            timeout=15,
            headers={"User-Agent": "TopTen/1.0"},
        )
        resp.raise_for_status()
        data = resp.json()
        return data.get("data", data)
    except Exception as e:
        print(f"  [Analyze] Pinksale detail fetch failed: {e}")
        return {}


def check_contract(address: str, chain: str = "eth") -> dict:
    """Check contract verification via Etherscan/BSCscan free API."""
    result = {"address": address, "verified": False, "source_available": False}
    if chain.lower() in ("bsc", "binance", "56"):
        api_url = "https://api.bscscan.com/api"
    else:
        api_url = "https://api.etherscan.io/api"
    try:
        resp = requests.get(
            api_url,
            params={
                "module":  "contract",
                "action":  "getsourcecode",
                "address": address,
                "apikey":  "YourApiKeyToken",
            },
            timeout=10,
        )
        resp.raise_for_status()
        data = resp.json()
        if data.get("status") == "1" and data.get("result"):
            src = data["result"][0]
            result["verified"]         = bool(src.get("SourceCode"))
            result["contract_name"]    = src.get("ContractName", "")
            result["compiler_version"] = src.get("CompilerVersion", "")
            result["source_available"] = bool(src.get("SourceCode"))
    except Exception as e:
        print(f"  [Analyze] Contract check failed: {e}")
    return result


def fetch_project_site(url: str) -> str:
    """Fetch project homepage and return first 2000 chars of cleaned text."""
    try:
        resp = requests.get(url, timeout=5, headers={"User-Agent": "Mozilla/5.0"})
        raw  = resp.text[:8000]
        clean = re.sub(r'<[^>]+>', ' ', raw)
        clean = re.sub(r'\s+', ' ', clean).strip()
        return clean[:2000]
    except Exception as e:
        print(f"  [Analyze] Site fetch failed: {e}")
        return ""


def custom_analyze(user_input: str, chain: str = "auto") -> dict:
    """Full pipeline: parse input, gather data, run AIVM, return result."""
    parsed     = parse_input_type(user_input)
    input_type = parsed["type"]
    raw_data   = {}
    project_name   = ""
    chain_detected = chain

    if input_type == "pinksale":
        launchpad_id   = parsed["id"]
        raw_data       = fetch_pinksale_details(launchpad_id)
        token          = raw_data.get("token", raw_data.get("saleToken", {}))
        project_name   = token.get("name", raw_data.get("name", f"Pinksale #{launchpad_id}"))
        chain_detected = str(raw_data.get("chain", raw_data.get("network", chain)))
        website = (raw_data.get("website")
                   or raw_data.get("projectInfo", {}).get("website", ""))
        if website:
            site_text = fetch_project_site(website)
            if site_text:
                raw_data["_site_excerpt"] = site_text

    elif input_type == "dxsale":
        raw_data     = {"platform": "DxSale", "url": user_input}
        project_name = "DxSale Presale"

    elif input_type == "contract":
        address      = parsed["address"]
        contract_info = check_contract(address, chain)
        raw_data     = contract_info
        project_name = contract_info.get("contract_name") or (address[:10] + "...")

    else:
        raw_data     = {"query": parsed.get("name", user_input)}
        project_name = parsed.get("name", user_input)

    user_prompt = (
        f"Presale Input: {user_input}\n"
        f"Input Type: {input_type}\n"
        f"Chain: {chain_detected}\n"
        f"Project Name: {project_name}\n\n"
        f"Gathered Data:\n{json.dumps(raw_data, indent=2, default=str)[:6000]}"
    )

    client = get_aivm_client()
    if not client:
        return {"success": False, "error": "AIVM analysis service temporarily unavailable."}

    try:
        raw_response = client.chat(CUSTOM_ANALYSIS_SYSTEM_PROMPT, user_prompt, timeout_secs=360)
        cleaned = re.sub(r"```(?:json)?", "", raw_response).strip().strip("`").strip()
        start = cleaned.find("{")
        end   = cleaned.rfind("}") + 1
        if start >= 0 and end > start:
            cleaned = cleaned[start:end]
        analysis = json.loads(cleaned)
        for key in ("score", "verdict", "green_flags", "red_flags", "analysis", "recommendation", "risk_breakdown"):
            if key not in analysis:
                if key == "risk_breakdown":
                    analysis["risk_breakdown"] = {
                        "tokenomics": 5, "team_transparency": 5,
                        "liquidity_safety": 5, "timing_risk": 5,
                    }
                else:
                    raise ValueError(f"Missing key: {key}")
        analysis["score"] = max(1, min(10, int(analysis["score"])))
        return {
            "success":      True,
            "input_type":   input_type,
            "project_name": project_name,
            "chain":        chain_detected,
            "raw_data":     raw_data,
            "analysis":     analysis,
        }
    except Exception as e:
        print(f"  [Analyze] Analysis failed: {e}")
        return {"success": False, "error": f"Analysis failed: {str(e)}"}


# ════════════════════════════════════════════════════════════════════════
# DATA FETCHING
# ════════════════════════════════════════════════════════════════════════

def fetch_pinksale() -> list:
    """Fetch live presales from Pinksale API. Returns list of dicts."""
    try:
        resp = requests.get(
            "https://api.pinksale.finance/api/v1/launchpad/list",
            params={"type": "launchpad", "status": "live", "page": 1, "pageSize": 20},
            timeout=20,
            headers={"User-Agent": "TopTen/1.0"},
        )
        resp.raise_for_status()
        data = resp.json()
        items = data.get("data", data.get("result", data.get("items", [])))
        if not isinstance(items, list):
            items = []
        presales = []
        for item in items[:20]:
            token = item.get("token", item.get("saleToken", {}))
            name   = token.get("name", item.get("name", "Unknown"))
            symbol = token.get("symbol", item.get("symbol", "???"))
            chain  = item.get("chain", item.get("network", item.get("chainId", "Unknown")))
            presale = {
                "id":              str(item.get("id", item.get("address", f"ps_{name}"))),
                "name":            name,
                "symbol":          symbol,
                "chain":           str(chain),
                "hard_cap":        str(item.get("hardCap", item.get("hard_cap", "N/A"))),
                "soft_cap":        str(item.get("softCap", item.get("soft_cap", "N/A"))),
                "presale_rate":    str(item.get("presaleRate", item.get("presale_rate", "N/A"))),
                "listing_rate":    str(item.get("listingRate", item.get("listing_rate", "N/A"))),
                "liquidity_pct":   str(item.get("liquidityPercent", item.get("liquidity_percent", "N/A"))),
                "liquidity_lock":  str(item.get("liquidityLockDays", item.get("liquidity_lock_days", "N/A"))) + " days",
                "total_raised":    str(item.get("totalRaised", item.get("total_raised", item.get("raised", "N/A")))),
                "start_time":      str(item.get("startTime", item.get("start_time", ""))),
                "end_time":        str(item.get("endTime", item.get("end_time", ""))),
                "source":          "pinksale",
                "raw_data":        item,
            }
            presales.append(presale)
        return presales
    except Exception as e:
        print(f"  [TopTen] Pinksale fetch failed: {e}")
        return []


def fetch_coingecko_trending() -> list:
    """Fallback: fetch trending coins from CoinGecko."""
    try:
        resp = requests.get(
            "https://api.coingecko.com/api/v3/search/trending",
            timeout=15,
            headers={"User-Agent": "TopTen/1.0"},
        )
        resp.raise_for_status()
        data  = resp.json()
        coins = data.get("coins", [])
        presales = []
        for entry in coins[:10]:
            item = entry.get("item", entry)
            presale = {
                "id":             str(item.get("id", item.get("coin_id", "cg_unknown"))),
                "name":           item.get("name", "Unknown"),
                "symbol":         item.get("symbol", "???").upper(),
                "chain":          item.get("platforms", {}) and list(item.get("platforms", {}).keys())[0] or "Multi",
                "hard_cap":       "N/A",
                "soft_cap":       "N/A",
                "presale_rate":   "N/A",
                "listing_rate":   "N/A",
                "liquidity_pct":  "N/A",
                "liquidity_lock": "N/A",
                "total_raised":   "N/A",
                "start_time":     "",
                "end_time":       "",
                "market_cap_rank": str(item.get("market_cap_rank", "N/A")),
                "price_btc":      str(item.get("price_btc", "N/A")),
                "score":          str(item.get("score", "N/A")),
                "source":         "coingecko_trending",
                "raw_data":       item,
            }
            presales.append(presale)
        return presales
    except Exception as e:
        print(f"  [TopTen] CoinGecko trending fetch failed: {e}")
        return []


def fetch_presales() -> tuple:
    """Try Pinksale first, fall back to CoinGecko. Returns (presales, source)."""
    presales = fetch_pinksale()
    if len(presales) >= 3:
        return presales[:10], "pinksale"

    print("  [TopTen] Pinksale returned <3 items, trying CoinGecko...")
    presales = fetch_coingecko_trending()
    if presales:
        return presales[:10], "coingecko_trending"

    print("  [TopTen] All data sources failed — returning empty list")
    return [], "none"


# ════════════════════════════════════════════════════════════════════════
# CACHE
# ════════════════════════════════════════════════════════════════════════

_cache_lock = threading.Lock()


def load_cache() -> dict:
    try:
        with open(CACHE_FILE, "r") as f:
            return json.load(f)
    except Exception:
        return {}


def save_cache(data: dict):
    with _cache_lock:
        with open(CACHE_FILE, "w") as f:
            json.dump(data, f, indent=2, default=str)


def cache_is_stale() -> bool:
    cache = load_cache()
    if not cache or "last_updated" not in cache:
        return True
    try:
        lu = datetime.fromisoformat(cache["last_updated"].replace("Z", "+00:00"))
        age = (datetime.now(timezone.utc) - lu).total_seconds() / 3600
        return age > CACHE_MAX_AGE_HOURS
    except Exception:
        return True


# ════════════════════════════════════════════════════════════════════════
# REFRESH LOGIC
# ════════════════════════════════════════════════════════════════════════

_refresh_lock    = threading.Lock()
_refresh_running = False


def refresh_presales():
    """Fetch presales, run AIVM analysis on each, save cache."""
    global _refresh_running
    with _refresh_lock:
        if _refresh_running:
            print("  [TopTen] Refresh already running — skipping")
            return
        _refresh_running = True

    try:
        print("  [TopTen] Starting presale refresh...")
        presales_raw, source = fetch_presales()

        if not presales_raw:
            print("  [TopTen] No presale data available — aborting refresh")
            return

        print(f"  [TopTen] Fetched {len(presales_raw)} presales from {source}")
        analyzed = []

        # Save "in progress" state immediately so frontend shows something
        save_cache({
            "last_updated": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
            "source":       source,
            "status":       "refreshing",
            "presales":     [],
        })

        for i, p in enumerate(presales_raw):
            print(f"  [TopTen] Analyzing {i+1}/{len(presales_raw)}: {p.get('name', '?')} ({p.get('symbol', '?')})")
            # Build clean dict for AIVM (exclude raw_data to keep prompt compact)
            data_for_analysis = {k: v for k, v in p.items() if k != "raw_data"}
            analysis = analyze_presale(data_for_analysis)

            entry = {
                "id":             p.get("id", f"item_{i}"),
                "name":           p.get("name", "Unknown"),
                "symbol":         p.get("symbol", "???"),
                "chain":          p.get("chain", "Unknown"),
                "hard_cap":       p.get("hard_cap", "N/A"),
                "soft_cap":       p.get("soft_cap", "N/A"),
                "presale_rate":   p.get("presale_rate", "N/A"),
                "listing_rate":   p.get("listing_rate", "N/A"),
                "liquidity_lock": p.get("liquidity_lock", "N/A"),
                "liquidity_pct":  p.get("liquidity_pct", "N/A"),
                "total_raised":   p.get("total_raised", "N/A"),
                "end_time":       p.get("end_time", ""),
                "source":         p.get("source", source),
                "analysis":       analysis,
            }
            analyzed.append(entry)

            # Save partial results after each presale so cards appear as they complete
            save_cache({
                "last_updated": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
                "source":       source,
                "status":       "refreshing" if i < len(presales_raw) - 1 else "complete",
                "presales":     analyzed,
            })
            print(f"  [TopTen] Saved partial cache ({len(analyzed)} so far)")

            # Small delay between AIVM calls to avoid nonce conflicts
            if i < len(presales_raw) - 1:
                time.sleep(3)

        print(f"  [TopTen] Refresh complete — {len(analyzed)} presales cached")

    except Exception as e:
        print(f"  [TopTen] Refresh failed: {e}")
    finally:
        with _refresh_lock:
            _refresh_running = False


# ════════════════════════════════════════════════════════════════════════
# FLASK APP
# ════════════════════════════════════════════════════════════════════════

app = Flask(__name__)


def _add_cors(response):
    response.headers["Access-Control-Allow-Origin"] = "*"
    response.headers["Access-Control-Allow-Methods"] = "GET, POST, OPTIONS"
    response.headers["Access-Control-Allow-Headers"] = "Content-Type"
    return response


@app.after_request
def after_request(response):
    return _add_cors(response)


@app.route("/", methods=["GET"])
def index():
    return jsonify({"app": "Top Ten", "description": "Daily AI Presale Analysis powered by Lightchain AIVM"})


@app.route("/health", methods=["GET"])
def health():
    cache = load_cache()
    return jsonify({
        "status":       "ok",
        "last_updated": cache.get("last_updated", "never"),
        "count":        len(cache.get("presales", [])),
        "source":       cache.get("source", "none"),
        "aivm":         bool(get_aivm_client()),
        "refresh_running": _refresh_running,
    })


@app.route("/api/presales", methods=["GET"])
def api_presales():
    cache = load_cache()
    if not cache:
        return jsonify({
            "last_updated": None,
            "source":       "none",
            "presales":     [],
            "message":      "Data not yet available — refresh in progress or scheduled for 6 AM Eastern.",
        })
    return jsonify(cache)


@app.route("/api/refresh", methods=["POST", "OPTIONS"])
def api_refresh():
    if request.method == "OPTIONS":
        return jsonify({}), 200
    threading.Thread(target=refresh_presales, daemon=True).start()
    return jsonify({"status": "refresh started"})


@app.route("/api/analyze", methods=["POST", "OPTIONS"])
def api_analyze():
    if request.method == "OPTIONS":
        return jsonify({}), 200
    try:
        body       = request.get_json(force=True, silent=True) or {}
        user_input = str(body.get("input", "")).strip()
        chain      = str(body.get("chain", "auto")).strip()
        if not user_input:
            return jsonify({"success": False, "error": "No input provided."})
        if len(user_input) > 500:
            return jsonify({"success": False, "error": "Input too long (max 500 characters)."})
        result = custom_analyze(user_input, chain)
        return jsonify(result)
    except Exception as e:
        print(f"  [Analyze] Endpoint error: {e}")
        return jsonify({"success": False, "error": "Server error — please try again."})


# ════════════════════════════════════════════════════════════════════════
# SCHEDULER + STARTUP
# ════════════════════════════════════════════════════════════════════════

def start_scheduler():
    scheduler = BackgroundScheduler(timezone=pytz.timezone("America/New_York"))
    scheduler.add_job(refresh_presales, "cron", hour=6, minute=0)
    scheduler.start()
    print("  [TopTen] Scheduler started — daily refresh at 6 AM Eastern")
    return scheduler


def startup_refresh():
    """Run refresh at startup if cache is missing or stale."""
    if cache_is_stale():
        print("  [TopTen] Cache is stale or missing — running startup refresh")
        threading.Thread(target=refresh_presales, daemon=True).start()
    else:
        print("  [TopTen] Cache is fresh — skipping startup refresh")


# ════════════════════════════════════════════════════════════════════════
# MAIN
# ════════════════════════════════════════════════════════════════════════

if __name__ == "__main__":
    port = int(os.environ.get("PORT", 5000))
    print(f"Top Ten server starting on port {port}...")

    # Init AIVM client in background
    def _init_aivm():
        client = get_aivm_client()
        if client:
            print(f"  [AIVM] Ready — wallet: {client._account.address}")
        else:
            print("  [AIVM] UNAVAILABLE — set LIGHTCHAIN_PRIVATE_KEY env var")
    threading.Thread(target=_init_aivm, daemon=True).start()

    start_scheduler()
    startup_refresh()
    app.run(host="0.0.0.0", port=port)
