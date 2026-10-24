// SPDX-License-Identifier: MIT
/**
 * Flow tests for index.html. No packages: Node's built-in test runner loads the
 * page, answers JSON-RPC itself, and checks the contract, the function, and the result.
 *
 *   node --test tests/exchange-flow.test.mjs
 *
 * Selectors are keccak256 of the MatchingOrderBook ABI, not copies of the page constants.
 * The fee-bearing market is the contract in github.com/k26dr/solidity-dex MatchingOrderBook.sol.
 * The plain signatures are that market with the fee fields removed.
 */
import assert from "node:assert/strict";
import fs from "node:fs";
import test from "node:test";
import vm from "node:vm";
import { fileURLToPath } from "node:url";

const HTML_PATH = fileURLToPath(new URL("../index.html", import.meta.url));

const TESTNET = {
  chainId: "0xb626",
  rpcUrl: "https://rpc.testnet.chain.robinhood.com",
  explorerUrl: "https://explorer.testnet.chain.robinhood.com",
  exchangeAddress: "0x065c85B4a344B6135E2005f01B3aeaE6034e0C04",
  wethAddress: "0x7943e237c7F95DA44E0301572D358911207852Fa",
  marketId: "0xac8bd66acee81d757189a757faafcb0e2f3caae8e60b417350b75e721af860b3",
};

const ACCOUNT = "0x1111111111111111111111111111111111111111";
const OTHER = "0x2222222222222222222222222222222222222222";
const BASE = "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
const QUOTE = "0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
const BANK = "0xcccccccccccccccccccccccccccccccccccccccc";
const FEE = "0xdddddddddddddddddddddddddddddddddddddddd";
const BLOCKED = "0x188d4ce22c76a2c2952bccef6a7e3c812fcbabcc";
const OVERRIDE = "0x9999999999999999999999999999999999999999";
const EXTRA_MARKET = "0x" + "ab".repeat(32);
const CREATED_MARKET = "0x" + "44".repeat(32);
const OTHER_MARKET = "0x" + "55".repeat(32);
const TX_HASH = "0x" + "11".repeat(32);
const FILL_HASH = "0x" + "22".repeat(32);

const BASE_MIN = 10n ** 18n;
const QUOTE_MIN = 10n * 10n ** 6n;
const ASK_QTY = 2n * 10n ** 18n;
const ASK_PRICE = 100n * 10n ** 6n;
const BID_QTY = 3n * 10n ** 18n;
const BID_PRICE = 90n * 10n ** 6n;

const SIGNATURES = {
  orderCounter: "orderCounter()",
  createMarketFee: "createMarket(address,address,uint256,uint256,uint256,uint256,address)",
  createMarketPlain: "createMarket(address,address,uint256,uint256)",
  placeOrder: "placeOrder(bytes32,uint8,uint256,uint256)",
  cancelOrder: "cancelOrder(bytes32,uint8,uint128)",
  getMarketIdFee: "getMarketId(address,address,uint256,uint256,uint256,uint256,address)",
  getMarketIdPlain: "getMarketId(address,address,uint256,uint256)",
  getMarketDetails: "getMarketDetails(bytes32)",
  getFirstOrderId: "getFirstOrderId(bytes32,uint8)",
  getOrderBook: "getOrderBook(bytes32,uint8,uint256)",
  balanceOf: "balanceOf(address)",
  allowance: "allowance(address,address)",
  approve: "approve(address,uint256)",
  decimals: "decimals()",
  symbol: "symbol()",
  deposit: "deposit()",
  withdraw: "withdraw(uint256)",
};

const EVENTS = {
  TOPIC_ORDER_FILL: "OrderFill(uint256,address,address,bytes32,uint256,uint256)",
  TOPIC_MARKET_FEE: "MarketCreated(bytes32,address,address,uint256,uint256,uint256,uint256,address,address)",
  TOPIC_MARKET_PLAIN: "MarketCreated(bytes32,address,address,uint256,uint256,address)",
};

const MASK = 0xffffffffffffffffn;
const ROT = [
  [0, 36, 3, 41, 18],
  [1, 44, 10, 45, 2],
  [62, 6, 43, 15, 61],
  [28, 55, 25, 21, 56],
  [27, 20, 39, 8, 14],
];
const RC = [
  0x0000000000000001n, 0x0000000000008082n, 0x800000000000808an, 0x8000000080008000n,
  0x000000000000808bn, 0x0000000080000001n, 0x8000000080008081n, 0x8000000000008009n,
  0x000000000000008an, 0x0000000000000088n, 0x0000000080008009n, 0x000000008000000an,
  0x000000008000808bn, 0x800000000000008bn, 0x8000000000008089n, 0x8000000000008003n,
  0x8000000000008002n, 0x8000000000000080n, 0x000000000000800an, 0x800000008000000an,
  0x8000000080008081n, 0x8000000000008080n, 0x0000000080000001n, 0x8000000080008008n,
];

function rotl(value, bits) {
  const shift = BigInt(bits);
  return ((value << shift) | (value >> (64n - shift))) & MASK;
}

function keccakF(state) {
  for (let round = 0; round < 24; round++) {
    const c = [0n, 0n, 0n, 0n, 0n];
    for (let x = 0; x < 5; x++) c[x] = state[x] ^ state[x + 5] ^ state[x + 10] ^ state[x + 15] ^ state[x + 20];
    for (let i = 0; i < 25; i++) state[i] = (state[i] ^ c[(i + 4) % 5] ^ rotl(c[(i + 1) % 5], 1)) & MASK;
    const next = Array(25).fill(0n);
    for (let x = 0; x < 5; x++) {
      for (let y = 0; y < 5; y++) next[y + 5 * ((2 * x + 3 * y) % 5)] = rotl(state[x + 5 * y], ROT[x][y]);
    }
    for (let y = 0; y < 5; y++) {
      for (let x = 0; x < 5; x++) {
        const index = x + 5 * y;
        state[index] = (next[index] ^ ((~next[((x + 1) % 5) + 5 * y]) & next[((x + 2) % 5) + 5 * y])) & MASK;
      }
    }
    state[0] = (state[0] ^ RC[round]) & MASK;
  }
}

function keccak256(value) {
  const bytes = typeof value === "string" ? Buffer.from(value) : Buffer.from(value);
  const rate = 136;
  const padded = Buffer.alloc(bytes.length + rate - (bytes.length % rate));
  bytes.copy(padded);
  padded[bytes.length] ^= 0x01;
  padded[padded.length - 1] ^= 0x80;
  const state = Array(25).fill(0n);
  for (let offset = 0; offset < padded.length; offset += rate) {
    for (let lane = 0; lane < 17; lane++) {
      let word = 0n;
      for (let byte = 0; byte < 8; byte++) word |= BigInt(padded[offset + lane * 8 + byte]) << BigInt(8 * byte);
      state[lane] ^= word;
    }
    keccakF(state);
  }
  const out = Buffer.alloc(32);
  for (let lane = 0; lane < 4; lane++) {
    let word = state[lane];
    for (let byte = 0; byte < 8; byte++) {
      out[lane * 8 + byte] = Number(word & 0xffn);
      word >>= 8n;
    }
  }
  return out.toString("hex");
}

function selectorOf(signature) {
  return keccak256(signature).slice(0, 8);
}

function topicOf(signature) {
  return "0x" + keccak256(signature);
}

const SEL = Object.fromEntries(Object.entries(SIGNATURES).map(([name, signature]) => [name, selectorOf(signature)]));
const TOPIC = Object.fromEntries(Object.entries(EVENTS).map(([name, signature]) => [name, topicOf(signature)]));

function word(value) {
  return BigInt(value).toString(16).padStart(64, "0");
}

function addrWord(value) {
  return value.toLowerCase().replace(/^0x/, "").padStart(64, "0");
}

function bytes32Word(value) {
  return value.toLowerCase().replace(/^0x/, "").padStart(64, "0");
}

function calldata(selector, args) {
  return "0x" + selector + args.map((part) => {
    if (typeof part === "string") return part.length === 66 ? bytes32Word(part) : addrWord(part);
    return word(part);
  }).join("");
}

function returns(words) {
  return "0x" + words.join("");
}

function textWord(text) {
  return Buffer.from(text, "utf8").toString("hex").padEnd(64, "0");
}

function revertData(message) {
  const bytes = Buffer.from(message, "utf8");
  const hex = bytes.toString("hex").padEnd(Math.ceil(bytes.length / 32) * 64, "0");
  return "0x08c379a0" + word(32) + word(bytes.length) + hex;
}

function encodeOrders(orders) {
  const words = [word(32), word(orders.length)];
  for (const order of orders) {
    words.push(addrWord(order.user), word(order.qty), word(order.price), word(order.next), word(order.prev));
  }
  return returns(words);
}

function selectorFromData(data) {
  return String(data || "").slice(2, 10).toLowerCase();
}

function argWord(data, index) {
  return "0x" + String(data).slice(10 + index * 64, 10 + (index + 1) * 64).toLowerCase();
}

class Element {
  constructor(tag) {
    this.tagName = String(tag || "div").toUpperCase();
    this.children = [];
    this.parentElement = null;
    this.attributes = new Map();
    this.listeners = {};
    this.style = {};
    this.id = "";
    this.value = "";
    this.checked = false;
    this.disabled = false;
    this.hidden = false;
    this.type = "";
    this.title = "";
    this.href = "";
    this.target = "";
    this.rel = "";
    this.colSpan = 1;
    this._className = "";
    this._text = "";
    this.classList = {
      contains: (name) => this._className.split(/\s+/).includes(name),
      add: (...names) => {
        const tokens = new Set(this._className.split(/\s+/).filter(Boolean));
        for (const name of names) tokens.add(name);
        this._className = [...tokens].join(" ");
      },
      remove: (...names) => {
        const drop = new Set(names);
        this._className = this._className.split(/\s+/).filter((name) => name && !drop.has(name)).join(" ");
      },
      toggle: (name, force) => {
        const has = this.classList.contains(name);
        const next = force === undefined ? !has : Boolean(force);
        if (next) this.classList.add(name);
        else this.classList.remove(name);
        return next;
      },
    };
  }

  get className() { return this._className; }
  set className(value) { this._className = value ? String(value) : ""; }
  get textContent() {
    if (this.children.length) return this.children.map((child) => child.textContent).join("");
    return this._text;
  }
  set textContent(value) {
    this._text = value == null ? "" : String(value);
    this.children = [];
  }
  get options() {
    return this.children.filter((child) => child.tagName === "OPTION");
  }

  setAttribute(name, value) { this.attributes.set(name, String(value)); }
  getAttribute(name) { return this.attributes.has(name) ? this.attributes.get(name) : null; }
  addEventListener(type, fn) { (this.listeners[type] ||= []).push(fn); }
  appendChild(child) {
    child.parentElement = this;
    this.children.push(child);
    return child;
  }
  append(...nodes) {
    for (const node of nodes) this.appendChild(node);
  }
  replaceChildren(...nodes) {
    this.children = [];
    this._text = "";
    for (const node of nodes) this.appendChild(node);
  }
  matches(selector) {
    if (selector.startsWith(".")) return this.classList.contains(selector.slice(1));
    const match = selector.match(/^([a-z]+)?\[([^\]]+)\]$/i);
    if (match) {
      if (match[1] && this.tagName !== match[1].toUpperCase()) return false;
      return this.attributes.has(match[2]);
    }
    return this.tagName === String(selector).toUpperCase();
  }
  closest(selector) {
    let node = this;
    while (node) {
      if (node.matches && node.matches(selector)) return node;
      node = node.parentElement;
    }
    return null;
  }
  querySelectorAll(selector) {
    const found = [];
    const walk = (node) => {
      for (const child of node.children) {
        if (child.matches(selector)) found.push(child);
        walk(child);
      }
    };
    walk(this);
    return found;
  }
}

function applyAttributes(element, source, ids) {
  const pattern = /([^\s=\/]+)(?:\s*=\s*(?:"([^"]*)"|'([^']*)'|([^\s"'>]+)))?/g;
  let match;
  while ((match = pattern.exec(source))) {
    const name = match[1].toLowerCase();
    const value = match[2] ?? match[3] ?? match[4] ?? "";
    if (name === "id") {
      element.id = value;
      ids.set(value, element);
    } else if (name === "class") element.className = value;
    else if (name === "hidden") element.hidden = true;
    else if (name === "disabled") element.disabled = true;
    else if (name === "type") element.type = value;
    else if (name === "href") element.href = value;
    else element.setAttribute(name, value === "" ? "" : value);
  }
}

function parseBody(html) {
  const bodyStart = html.indexOf("<body");
  const bodyOpen = html.indexOf(">", bodyStart);
  const scriptAt = html.indexOf("<script>", bodyOpen);
  const bodyHtml = html.slice(bodyOpen + 1, scriptAt);
  const ids = new Map();
  const root = new Element("body");
  const stack = [root];
  const voidTags = new Set(["input", "br", "img", "meta", "link", "source", "wbr", "hr"]);
  const pattern = /<!--[\s\S]*?-->|<\/([a-zA-Z0-9]+)\s*>|<([a-zA-Z0-9]+)([^>]*?)(\/?)>/g;
  let match;
  while ((match = pattern.exec(bodyHtml))) {
    if (match[0].startsWith("<!--")) continue;
    if (match[1]) {
      const name = match[1].toUpperCase();
      while (stack.length > 1 && stack[stack.length - 1].tagName !== name) stack.pop();
      if (stack.length > 1) stack.pop();
      continue;
    }
    const element = new Element(match[2]);
    applyAttributes(element, match[3] || "", ids);
    stack[stack.length - 1].appendChild(element);
    if (!match[4] && !voidTags.has(match[2].toLowerCase())) stack.push(element);
  }
  return { root, ids };
}

function pageSource(html) {
  const start = html.indexOf("<script>");
  const end = html.lastIndexOf("</script>");
  const source = html.slice(start + "<script>".length, end);
  return source.replace(/\nbind\(\);\s*\nboot\(\);\s*$/, `
globalThis.__page = {
  get state() { return state; },
  SEL,
  CHAINS,
  TOPIC_ORDER_FILL,
};
bind();
globalThis.__booted = boot();
`);
}

function memoryStorage(initial) {
  const map = new Map(Object.entries(initial || {}));
  return {
    getItem(key) { return map.has(key) ? map.get(key) : null; },
    setItem(key, value) { map.set(String(key), String(value)); },
    removeItem(key) { map.delete(key); },
  };
}

function dispatch(node, type) {
  const event = { target: node };
  let current = node;
  while (current) {
    for (const fn of current.listeners[type] || []) fn(event);
    current = current.parentElement;
  }
}

function tableRows(document, id) {
  return [...document.getElementById(id).children].map((row) =>
    [...row.children].map((cell) => cell.textContent.trim()));
}

function bookLevels(document, id) {
  return [...document.getElementById(id).children]
    .filter((node) => node.className.split(/\s+/).includes("level"))
    .map((node) => [...node.children]
      .filter((child) => !child.className.split(/\s+/).includes("bar"))
      .map((child) => child.textContent));
}

function emptyDetails(kind) {
  return returns(Array(kind === "plain" ? 5 : 8).fill(word(0)));
}

function marketDetails(kind) {
  if (kind === "plain") {
    return returns([addrWord(BASE), addrWord(QUOTE), word(BASE_MIN), word(QUOTE_MIN), addrWord(BANK)]);
  }
  return returns([
    addrWord(BASE), addrWord(QUOTE), word(BASE_MIN), word(QUOTE_MIN),
    word(30), word(10000), addrWord(FEE), addrWord(BANK),
  ]);
}

async function loadPage(options = {}) {
  const html = fs.readFileSync(HTML_PATH, "utf8");
  const parsed = parseBody(html);
  const storageKey = "zigzag-exchange-v1:" + (options.chainId || TESTNET.chainId) + ":exchange";
  const initial = {};
  if (options.chainKey) initial["zigzag-exchange-v1:network"] = options.chainKey;
  if (options.savedExchange) initial[storageKey] = options.savedExchange;
  const localStorage = memoryStorage(initial);
  const calls = [];
  const world = {
    kind: options.kind || "fee",
    code: options.code === undefined ? "0x60016000" : options.code,
    account: options.account === undefined ? ACCOUNT : options.account,
    walletChainId: options.walletChainId || TESTNET.chainId,
    revertPlace: Boolean(options.revertPlace),
    marketLogs: options.marketLogs || [],
    receiptLogs: options.receiptLogs || [],
    validMarkets: new Set([TESTNET.marketId, ...(options.extraMarkets || [])].map((id) => id.toLowerCase())),
    fills: options.fills === undefined ? defaultFills() : options.fills,
    balance: new Map([
      [BASE, 5n * 10n ** 18n],
      [QUOTE, 1000n * 10n ** 6n],
      [TESTNET.wethAddress.toLowerCase(), 4n * 10n ** 18n],
    ]),
    allowance: new Map([
      [BASE, 0n],
      [QUOTE, 1000n * 10n ** 6n],
    ]),
    ethBalance: 2n * 10n ** 18n,
    symbol: new Map([[BASE, "ZZB"], [QUOTE, "ZZQ"]]),
    decimals: new Map([[BASE, 18], [QUOTE, 6]]),
  };

  function answerCall(to, data) {
    const address = String(to || "").toLowerCase();
    const selector = selectorFromData(data);
    const id = argWord(data, 0);
    if (address === TESTNET.wethAddress.toLowerCase() && selector === SEL.balanceOf) return returns([word(world.balance.get(address) || 0n)]);
    if (world.symbol.has(address) || address === BASE || address === QUOTE) {
      if (selector === SEL.symbol) return "0x" + textWord(world.symbol.get(address) || "TOK");
      if (selector === SEL.decimals) return returns([word(world.decimals.get(address) ?? 18)]);
      if (selector === SEL.balanceOf) return returns([word(world.balance.get(address) || 0n)]);
      if (selector === SEL.allowance) return returns([word(world.allowance.get(address) || 0n)]);
      return "0x";
    }
    if (selector === SEL.orderCounter) return options.badCounter ? "0x" : returns([word(1)]);
    if (selector === SEL.getMarketDetails) {
      return world.validMarkets.has(id) ? marketDetails(world.kind) : emptyDetails(world.kind);
    }
    if (selector === SEL.getFirstOrderId) {
      const side = BigInt(argWord(data, 1));
      return returns([word(side === 1n ? 7 : 4)]);
    }
    if (selector === SEL.getOrderBook) {
      const side = BigInt(argWord(data, 1));
      const order = side === 1n
        ? { user: ACCOUNT, qty: ASK_QTY, price: ASK_PRICE, next: 0, prev: 0 }
        : { user: OTHER, qty: BID_QTY, price: BID_PRICE, next: 0, prev: 0 };
      return encodeOrders([order]);
    }
    if (selector === SEL.getMarketIdFee || selector === SEL.getMarketIdPlain) return returns([bytes32Word(CREATED_MARKET)]);
    return "0x";
  }

  function answerRpc(method, params) {
    if (method === "eth_getCode") return world.code;
    if (method === "eth_blockNumber") return "0x4000";
    if (method === "eth_getBalance") return "0x" + world.ethBalance.toString(16);
    if (method === "eth_getTransactionReceipt") {
      return { status: "0x1", transactionHash: params[0], logs: world.receiptLogs };
    }
    if (method === "eth_getLogs") {
      const filter = params[0] || {};
      const topics = filter.topics || [];
      const topic0 = String(topics[0] || "").toLowerCase();
      if (topic0 === TOPIC.TOPIC_MARKET_FEE.toLowerCase() || topic0 === TOPIC.TOPIC_MARKET_PLAIN.toLowerCase()) {
        return world.marketLogs;
      }
      if (topic0 === TOPIC.TOPIC_ORDER_FILL.toLowerCase()) {
        const accountTopic = "0x" + ACCOUNT.slice(2).padStart(64, "0");
        if (topics[2] === accountTopic || topics[3] === accountTopic) return world.fills;
        return [];
      }
      return [];
    }
    if (method === "eth_call") {
      if (world.revertPlace && params[0].from && selectorFromData(params[0].data) === SEL.placeOrder) {
        const error = new Error("execution reverted");
        error.code = 3;
        error.data = revertData("order was too small to post. ran as fill or kill and failed to fill.");
        throw error;
      }
      if (options.badCounter && selectorFromData(params[0].data) === SEL.orderCounter) return "0x";
      return answerCall(params[0].to, params[0].data);
    }
    throw new Error("Unexpected RPC method " + method);
  }

  const window = options.noWallet ? {} : {
    ethereum: {
      on(event, fn) { (this.listeners[event] ||= []).push(fn); },
      listeners: {},
      async request({ method, params }) {
        calls.push({ channel: "wallet", method, params, url: "" });
        if (method === "eth_chainId") return world.walletChainId;
        if (method === "eth_accounts" || method === "eth_requestAccounts") return world.account ? [world.account] : [];
        if (method === "eth_call" || method === "eth_getBalance" || method === "eth_getCode" || method === "eth_getLogs" || method === "eth_blockNumber" || method === "eth_getTransactionReceipt") {
          return answerRpc(method, params);
        }
        if (method === "eth_sendTransaction") {
          const tx = params[0];
          if (selectorFromData(tx.data) === SEL.approve) {
            world.allowance.set(String(tx.to).toLowerCase(), BigInt(argWord(tx.data, 1)));
          }
          return TX_HASH;
        }
        if (method === "wallet_switchEthereumChain" || method === "wallet_addEthereumChain") return null;
        throw new Error("Unexpected wallet method " + method);
      },
    },
  };

  const document = {
    visibilityState: "visible",
    activeElement: null,
    body: parsed.root,
    createElement(tag) { return new Element(tag); },
    getElementById(id) { return parsed.ids.get(id) || null; },
    addEventListener(type, fn) { parsed.root.addEventListener(type, fn); },
  };

  const context = {
    console,
    TextDecoder,
    AbortController,
    URL,
    setTimeout,
    clearTimeout,
    setInterval() { return 1; },
    clearInterval() {},
    localStorage,
    window,
    document,
    fetch: async (url, init) => {
      const body = JSON.parse(init.body);
      calls.push({ channel: "rpc", method: body.method, params: body.params, url: String(url) });
      try {
        const result = answerRpc(body.method, body.params);
        return { ok: true, status: 200, json: async () => ({ jsonrpc: "2.0", id: body.id, result }) };
      } catch (error) {
        return {
          ok: true,
          status: 200,
          json: async () => ({
            jsonrpc: "2.0",
            id: body.id,
            error: { code: error.code || -32000, message: error.message, data: error.data },
          }),
        };
      }
    },
  };

  vm.createContext(context);
  vm.runInContext(pageSource(html), context, { filename: "index.html" });
  await context.__booted;
  const $ = (id) => document.getElementById(id);
  return {
    state: context.__page.state,
    page: context.__page,
    document,
    calls,
    world,
    localStorage,
    $,
    setInput(id, value) {
      const node = $(id);
      node.value = value;
      for (const fn of node.listeners.input || []) fn({ target: node });
    },
    click(id) { dispatch($(id), "click"); },
    clickNode(node) { dispatch(node, "click"); },
  };
}

function defaultFills() {
  const accountTopic = "0x" + addrWord(ACCOUNT);
  const otherTopic = "0x" + addrWord(OTHER);
  const orderTopic = "0x" + word(42);
  return [
    {
      topics: [TOPIC.TOPIC_ORDER_FILL, orderTopic, accountTopic, otherTopic],
      data: "0x" + bytes32Word(TESTNET.marketId) + word(10n ** 18n) + word(ASK_PRICE),
      transactionHash: FILL_HASH,
      logIndex: "0x1",
      blockNumber: "0x20",
    },
    {
      topics: [TOPIC.TOPIC_ORDER_FILL, "0x" + word(9), otherTopic, accountTopic],
      data: "0x" + bytes32Word(OTHER_MARKET) + word(10n ** 18n) + word(ASK_PRICE),
      transactionHash: "0x" + "33".repeat(32),
      logIndex: "0x1",
      blockNumber: "0x30",
    },
  ];
}

function rpcCalls(api, method) {
  return api.calls.filter((call) => call.channel === "rpc" && call.method === method);
}

function sends(api) {
  return api.calls.filter((call) => call.channel === "wallet" && call.method === "eth_sendTransaction");
}

function callsWithSelector(api, selector) {
  return rpcCalls(api, "eth_call").filter((call) => selectorFromData(call.params[0].data) === selector);
}

async function settle() {
  await new Promise((resolve) => setTimeout(resolve, 0));
}

async function waitUntil(fn, message) {
  const started = Date.now();
  while (Date.now() - started < 2000) {
    if (fn()) return;
    await new Promise((resolve) => setTimeout(resolve, 0));
  }
  throw new Error(message || "timed out");
}

test("keccak256 matches the empty-string and transfer vectors", () => {
  assert.equal(keccak256(""), "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470");
  assert.equal(selectorOf("transfer(address,uint256)"), "a9059cbb");
});

test("page selectors and event topics are the MatchingOrderBook functions the page calls", async () => {
  const api = await loadPage();
  const used = [
    "orderCounter", "placeOrder", "cancelOrder", "getMarketDetails", "getFirstOrderId", "getOrderBook",
    "balanceOf", "allowance", "approve", "decimals", "symbol", "deposit", "withdraw",
  ];
  for (const name of used) {
    assert.equal(api.page.SEL[name], SEL[name], name + " should be " + SIGNATURES[name]);
  }
  for (const name of ["createMarketFee", "createMarketPlain", "getMarketIdFee", "getMarketIdPlain"]) {
    assert.equal(api.page.SEL[name], undefined, name);
  }
  assert.equal(api.page.TOPIC_ORDER_FILL, TOPIC.TOPIC_ORDER_FILL);
  assert.equal(api.page.TOPIC_MARKET_FEE, undefined);
  assert.equal(api.page.TOPIC_MARKET_PLAIN, undefined);
  assert.equal(api.$("create-market"), null);
  assert.equal(api.$("compute-id"), null);
  assert.equal(api.$("market-id-input"), null);
  assert.equal(api.$("exchange-address"), null);
});

test("Robinhood testnet is pinned and chains without a deployment have no exchange", async () => {
  const api = await loadPage();
  const testnet = api.page.CHAINS.find((chain) => chain.key === "robinhood-testnet");
  assert.equal(testnet.chainId, TESTNET.chainId);
  assert.equal(testnet.rpcUrl, TESTNET.rpcUrl);
  assert.equal(testnet.explorerUrl, TESTNET.explorerUrl);
  assert.equal(testnet.exchangeAddress, TESTNET.exchangeAddress);
  assert.equal(testnet.wethAddress, TESTNET.wethAddress);
  assert.deepEqual([...testnet.marketIds], [TESTNET.marketId]);
  for (const chain of api.page.CHAINS.filter((item) => item.key !== "robinhood-testnet")) {
    assert.equal(chain.exchangeAddress, "", chain.chainName + " should not ship an exchange address");
  }
});

test("boot reads the pinned exchange through the testnet RPC", async () => {
  const api = await loadPage();
  assert.equal(api.state.mode, "live", api.state.banner);
  assert.equal(api.state.interfaceKind, "fee");
  for (const call of api.calls.filter((item) => item.channel === "rpc")) {
    assert.equal(call.url, TESTNET.rpcUrl);
  }
  const code = rpcCalls(api, "eth_getCode");
  assert.equal(code.length > 0, true);
  assert.equal(code[0].params[0].toLowerCase(), TESTNET.exchangeAddress.toLowerCase());
  const probe = callsWithSelector(api, SEL.getMarketDetails);
  assert.equal(probe[0].params[0].to.toLowerCase(), TESTNET.exchangeAddress.toLowerCase());
  assert.equal(argWord(probe[0].params[0].data, 0), "0x" + "0".repeat(64));
  const counter = callsWithSelector(api, SEL.orderCounter);
  assert.equal(counter[0].params[0].to.toLowerCase(), TESTNET.exchangeAddress.toLowerCase());
  assert.equal(counter[0].params[0].data, "0x" + SEL.orderCounter);
});

test("market details from getMarketDetails are what the form shows", async () => {
  const api = await loadPage();
  const detail = callsWithSelector(api, SEL.getMarketDetails).find((call) => argWord(call.params[0].data, 0) === TESTNET.marketId);
  assert.ok(detail, "getMarketDetails was not called for the pinned market");
  assert.equal(detail.params[0].to.toLowerCase(), TESTNET.exchangeAddress.toLowerCase());
  assert.equal(api.$("market-list").textContent, "ZZB/ZZQ");
  assert.equal(api.$("market-meta").textContent, "Min 1 ZZB · 10 ZZQ");
  assert.equal(api.$("min-label").textContent, "Minimum post 1 ZZB and 10 ZZQ");
  assert.equal(api.$("fee-label").textContent, "Market fee 0.3% (30/10000) to 0xdddd…dddd");
  assert.equal(api.$("spender-label").textContent, "Spender " + TESTNET.exchangeAddress.toLowerCase());
  assert.match(api.$("banner").textContent, /Robinhood Chain Testnet/);
  assert.match(api.$("banner").textContent, /0x065c…0c04/);
});

test("the order book is read from the exchange and the prices are the contract values", async () => {
  const api = await loadPage();
  for (const side of [0n, 1n]) {
    const head = callsWithSelector(api, SEL.getFirstOrderId).find((call) => BigInt(argWord(call.params[0].data, 1)) === side);
    const book = callsWithSelector(api, SEL.getOrderBook).find((call) => BigInt(argWord(call.params[0].data, 1)) === side);
    assert.equal(head.params[0].to.toLowerCase(), TESTNET.exchangeAddress.toLowerCase());
    assert.equal(book.params[0].to.toLowerCase(), TESTNET.exchangeAddress.toLowerCase());
    assert.equal(argWord(head.params[0].data, 0), TESTNET.marketId);
    assert.equal(argWord(book.params[0].data, 0), TESTNET.marketId);
    assert.equal(BigInt(argWord(book.params[0].data, 2)), 25n);
  }
  assert.deepEqual(bookLevels(api.document, "asks"), [["100", "2", "200"]]);
  assert.deepEqual(bookLevels(api.document, "bids"), [["90", "3", "270"]]);
  assert.equal(api.$("asks").querySelectorAll(".level")[0].children[0].style.width, "100%");
  assert.equal(api.$("spread").children[1].textContent, "10");
  assert.deepEqual(tableRows(api.document, "orders-body"), [["Sell", "100", "2 ZZB", "2 ZZB", "Cancel"]]);
});

test("balances come from the token contracts and allowance names the exchange as spender", async () => {
  const api = await loadPage();
  const balance = callsWithSelector(api, SEL.balanceOf).find((call) => call.params[0].to.toLowerCase() === BASE);
  const allowance = callsWithSelector(api, SEL.allowance).find((call) => call.params[0].to.toLowerCase() === QUOTE);
  assert.equal(argWord(balance.params[0].data, 0), "0x" + addrWord(ACCOUNT));
  assert.equal(argWord(allowance.params[0].data, 0), "0x" + addrWord(ACCOUNT));
  assert.equal(argWord(allowance.params[0].data, 1), "0x" + addrWord(TESTNET.exchangeAddress));
  assert.deepEqual(tableRows(api.document, "balance-body"), [
    ["ZZB", "5", "2", "5", "0"],
    ["ZZQ", "1000", "0", "1000", "1000"],
  ]);
  assert.equal(api.$("eth-balance").textContent, "ETH 2");
  assert.equal(api.$("weth-balance").textContent, "WETH 4");
  assert.equal(api.$("weth-contract").textContent, "WETH " + TESTNET.wethAddress);
});

test("a buy is placeOrder on the pinned exchange and the receipt is linked", async () => {
  const api = await loadPage();
  api.setInput("price-input", "100");
  api.setInput("amount-input", "2");
  assert.equal(api.$("total-output").textContent, "Total 200 ZZQ");
  assert.equal(api.$("place-button").disabled, false);
  api.click("place-button");
  await settle();
  const tx = sends(api);
  assert.equal(tx.length, 1);
  assert.equal(tx[0].params[0].from, ACCOUNT);
  assert.equal(tx[0].params[0].to.toLowerCase(), TESTNET.exchangeAddress.toLowerCase());
  assert.equal(tx[0].params[0].value, "0x0");
  assert.equal(tx[0].params[0].data, calldata(SEL.placeOrder, [TESTNET.marketId, 0n, ASK_QTY, ASK_PRICE]));
  const simulated = callsWithSelector(api, SEL.placeOrder).filter((call) => call.params[0].from);
  assert.equal(simulated.length > 0, true);
  assert.equal(simulated.at(-1).params[0].data, tx[0].params[0].data);
  assert.ok(api.calls.indexOf(simulated.at(-1)) < api.calls.indexOf(tx[0]));
  assert.equal(api.$("status").textContent, "Transaction confirmed.");
  assert.equal(api.$("tx-link").querySelectorAll("a")[0].href, TESTNET.explorerUrl + "/tx/" + TX_HASH);
});

test("a sell approves the base token for the exchange for the exact order amount", async () => {
  const api = await loadPage();
  api.click("side-sell");
  api.setInput("price-input", "100");
  api.setInput("amount-input", "2");
  assert.equal(api.$("place-button").disabled, true);
  assert.equal(api.$("approve-button").disabled, false);
  assert.equal(api.$("approve-button").textContent, "Approve ZZB");
  api.click("approve-button");
  await settle();
  const tx = sends(api);
  assert.equal(tx.length, 1);
  assert.equal(tx[0].params[0].to.toLowerCase(), BASE);
  assert.equal(tx[0].params[0].value, "0x0");
  assert.equal(tx[0].params[0].data, calldata(SEL.approve, [TESTNET.exchangeAddress, ASK_QTY]));
  assert.equal(api.$("allowance-label").textContent, "Allowance 2 ZZB");
});

test("a buy approves the quote token, and reset allowance sends zero", async () => {
  const api = await loadPage();
  api.setInput("price-input", "100");
  api.setInput("amount-input", "20");
  assert.equal(api.$("place-button").disabled, true);
  assert.equal(api.$("reset-allowance").hidden, false);
  api.click("approve-button");
  await settle();
  assert.equal(sends(api)[0].params[0].to.toLowerCase(), QUOTE);
  assert.equal(sends(api)[0].params[0].data, calldata(SEL.approve, [TESTNET.exchangeAddress, 2000n * 10n ** 6n]));
  assert.equal(api.$("allowance-label").textContent, "Allowance 2000 ZZQ");
  assert.equal(api.$("place-button").disabled, false);

  api.world.allowance.set(QUOTE, 1000n * 10n ** 6n);
  api.setInput("amount-input", "20");
  api.click("reset-allowance");
  await settle();
  assert.equal(sends(api).at(-1).params[0].to.toLowerCase(), QUOTE);
  assert.equal(sends(api).at(-1).params[0].data, calldata(SEL.approve, [TESTNET.exchangeAddress, 0n]));
});

test("cancel sends cancelOrder for the resting order id to the exchange", async () => {
  const api = await loadPage();
  const button = api.$("orders-body").querySelectorAll("button[data-order-id]")[0];
  assert.equal(button.getAttribute("data-order-id"), "7");
  assert.equal(button.getAttribute("data-side"), "1");
  api.clickNode(button);
  await settle();
  const tx = sends(api);
  assert.equal(tx.length, 1);
  assert.equal(tx[0].params[0].to.toLowerCase(), TESTNET.exchangeAddress.toLowerCase());
  assert.equal(tx[0].params[0].data, calldata(SEL.cancelOrder, [TESTNET.marketId, 1n, 7n]));
});

test("wrap sends deposit value to WETH and unwrap sends withdraw", async () => {
  const api = await loadPage();
  api.setInput("wrap-amount", "1.5");
  api.click("wrap-button");
  await settle();
  assert.equal(sends(api)[0].params[0].to, TESTNET.wethAddress);
  assert.equal(sends(api)[0].params[0].data, "0x" + SEL.deposit);
  assert.equal(sends(api)[0].params[0].value, "0x" + (15n * 10n ** 17n).toString(16));

  api.click("unwrap-button");
  await settle();
  assert.equal(sends(api)[1].params[0].to, TESTNET.wethAddress);
  assert.equal(sends(api)[1].params[0].data, calldata(SEL.withdraw, [15n * 10n ** 17n]));
  assert.equal(sends(api)[1].params[0].value, "0x0");
});

test("a reverted simulation is shown and nothing is sent", async () => {
  const api = await loadPage({ revertPlace: true });
  api.setInput("price-input", "100");
  api.setInput("amount-input", "2");
  api.click("place-button");
  await settle();
  assert.equal(sends(api).length, 0);
  assert.equal(api.$("status").textContent, "order was too small to post. ran as fill or kill and failed to fill.");
});

test("only the published market is listed, even if another market exists on the contract", async () => {
  const api = await loadPage({
    extraMarkets: [EXTRA_MARKET],
    marketLogs: [{
      address: TESTNET.exchangeAddress,
      topics: [TOPIC.TOPIC_MARKET_FEE, EXTRA_MARKET],
      data: "0x" + addrWord(BASE),
    }],
    savedExchange: OVERRIDE,
  });
  assert.equal(api.state.mode, "live");
  assert.equal(api.state.markets.length, 1);
  assert.equal(api.state.markets[0].id, TESTNET.marketId);
  assert.equal(api.$("market-list").textContent, "ZZB/ZZQ");
  assert.equal(callsWithSelector(api, SEL.getMarketDetails).some((call) => argWord(call.params[0].data, 0) === EXTRA_MARKET), false);
  assert.equal(callsWithSelector(api, SEL.createMarketFee).length, 0);
  assert.equal(callsWithSelector(api, SEL.getMarketIdFee).length, 0);
  assert.equal(rpcCalls(api, "eth_getCode")[0].params[0].toLowerCase(), TESTNET.exchangeAddress.toLowerCase());
  api.setInput("price-input", "100");
  api.setInput("amount-input", "2");
  api.click("place-button");
  await settle();
  assert.equal(sends(api)[0].params[0].to.toLowerCase(), TESTNET.exchangeAddress.toLowerCase());
});

test("fills show the OrderFill order, maker, taker, size, price, and total for this market", async () => {
  const api = await loadPage();
  assert.equal(api.state.fills.length, 2);
  assert.deepEqual(tableRows(api.document, "fills-body"), [[
    "42",
    "0x1111…1111",
    "0x2222…2222",
    "1 ZZB",
    "100",
    "100 ZZQ",
    "Tx",
  ]]);
  const maker = api.$("fills-body").children[0].children[1];
  assert.equal(maker.className, "you");
  assert.equal(api.$("fills-body").querySelectorAll("a")[0].href, TESTNET.explorerUrl + "/tx/" + FILL_HASH);
  assert.match(api.$("fills-note").textContent, /8000 blocks/);
  const fillLogs = rpcCalls(api, "eth_getLogs").filter((call) => String(call.params[0].topics[0]).toLowerCase() === TOPIC.TOPIC_ORDER_FILL);
  assert.equal(fillLogs.length > 0, true);
  assert.equal(fillLogs[0].params[0].address.toLowerCase(), TESTNET.exchangeAddress.toLowerCase());
});

test("clicking a book level fills the price, and max uses the wallet balance", async () => {
  const api = await loadPage();
  api.clickNode(api.$("asks").querySelectorAll(".level")[0]);
  assert.equal(api.$("price-input").value, "100");
  api.click("max-amount");
  assert.equal(api.$("amount-input").value, "10");
  api.click("side-sell");
  api.click("max-amount");
  assert.equal(api.$("amount-input").value, "5");
});

test("an order below the minimum is not sent until fill-or-kill is confirmed", async () => {
  const api = await loadPage();
  api.setInput("price-input", "100");
  api.setInput("amount-input", "0.1");
  assert.equal(api.$("fok-row").hidden, false);
  assert.equal(api.$("place-button").disabled, true);
  api.$("fok-check").checked = true;
  for (const fn of api.$("fok-check").listeners.change || []) fn({ target: api.$("fok-check") });
  assert.equal(api.$("place-button").disabled, false);
  api.click("place-button");
  await settle();
  assert.equal(sends(api)[0].params[0].data, calldata(SEL.placeOrder, [TESTNET.marketId, 0n, 10n ** 17n, ASK_PRICE]));
});

test("the book still loads with no wallet, and no transaction is sent", async () => {
  const api = await loadPage({ noWallet: true, account: null });
  assert.equal(api.state.mode, "live");
  assert.deepEqual(bookLevels(api.document, "asks"), [["100", "2", "200"]]);
  assert.equal(api.$("wallet-button").textContent, "No wallet");
  assert.match(tableRows(api.document, "balance-body")[0][0], /Connect a wallet on Robinhood Chain Testnet/);
  assert.equal(api.$("place-button").disabled, true);
  assert.equal(sends(api).length, 0);
});

test("a contract that fails the probe stays in demo and cannot send", async () => {
  const api = await loadPage({ code: "0x" });
  assert.equal(api.state.mode, "demo");
  assert.match(api.$("banner").textContent, /Demo data/);
  assert.equal(api.$("place-button").disabled, true);
  api.click("place-button");
  await settle();
  assert.equal(sends(api).length, 0);
  assert.match(api.$("status").textContent, /disabled/);
});

test("the wrong wallet network does not send a transaction", async () => {
  const api = await loadPage({ walletChainId: "0x1" });
  assert.equal(api.state.mode, "live");
  api.setInput("price-input", "100");
  api.setInput("amount-input", "2");
  assert.equal(api.$("place-button").disabled, true);
  api.click("place-button");
  await settle();
  assert.equal(sends(api).length, 0);
  assert.match(api.$("status").textContent, /Wrong network/);
});

test("a saved exchange address is ignored", async () => {
  const blocked = await loadPage({ savedExchange: BLOCKED });
  assert.equal(blocked.state.mode, "live");
  const blockedCode = rpcCalls(blocked, "eth_getCode").map((call) => call.params[0].toLowerCase());
  assert.equal(blockedCode.includes(BLOCKED), false);
  assert.equal(blockedCode.includes(TESTNET.exchangeAddress.toLowerCase()), true);

  const override = await loadPage({ savedExchange: OVERRIDE });
  override.setInput("price-input", "100");
  override.setInput("amount-input", "2");
  override.click("place-button");
  await settle();
  assert.equal(rpcCalls(override, "eth_getCode")[0].params[0].toLowerCase(), TESTNET.exchangeAddress.toLowerCase());
  assert.equal(sends(override)[0].params[0].to.toLowerCase(), TESTNET.exchangeAddress.toLowerCase());
});

test("Ethereum has no published exchange, so boot does not call one", async () => {
  const api = await loadPage({ chainKey: "ethereum", chainId: "0x1", account: null });
  assert.equal(api.state.mode, "demo");
  assert.equal(rpcCalls(api, "eth_call").length, 0);
  assert.equal(rpcCalls(api, "eth_getCode").length, 0);
  assert.equal(sends(api).length, 0);
});

test("a plain market shows that no fee is stored", async () => {
  const api = await loadPage({ kind: "plain" });
  assert.equal(api.state.mode, "live", api.state.blockReason);
  assert.equal(api.state.interfaceKind, "plain");
  assert.equal(api.$("fee-label").textContent, "Market fee is not stored on this deployment.");
  assert.equal(callsWithSelector(api, SEL.createMarketFee).length, 0);
  assert.equal(callsWithSelector(api, SEL.createMarketPlain).length, 0);
  assert.equal(sends(api).length, 0);
});
