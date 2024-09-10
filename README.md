# MlesTalk WebWorker

MlesTalk WebWorker is an open source Mles (Modern Lightweight channEl Service) WebSocket client layer protocol implementation written in JavaScript. MlesTalk WebWorker can be used independently by any application over its messaging application interface. It is used as part of [MlesTalk](https://mles.io/app.html) Android application.

Messages using MlesTalk WebWorker are sent on Transport Layer Security (TLS) [1] protected connection by default which should be secure.

In addition to transport-level TLS encryption, it is secured by [Zpinc protocol](https://github.com/ZpincDev/zpinc-webworker/raw/master/zpinc_paper.pdf) for message authentication, integrity and confidentiality. Even though Zpinc protocol should be safe, it is not audited. It is open-source, so you can check the code yourself, please report any issues! Pro bono professional auditors welcome as well!

Please see https://mles.io for details about Mles protocol.

## MlesTalk WebWorker Messaging API

### Init message
```
/**
 * Initialize Mles WebSocket connection
 *
 * @param  init {String}              IN: command parameter "init"
 * @param  data {String}              IN: data, null for "init"
 * @param  addr {String}              IN: TCP/IP address to connect to
 * @param  port {String}              IN: TCP/IP port to connect to
 * @param  uid {String}               IN: Mles User Id
 * @param  channel {String}           IN: Mles Channel
 * @param  key {String}               IN: Encryption key
 */
 webWorker.postMessage[("init", data, addr, port, uid, channel, key)]
```
### Init/Reconnect message receive
```
/**
 * Mles WebSocket connection init receive after successful WebSocket initialization
 *
 * @param  init {String}              OUT: command parameter of receive "init"
 * @param  uid {String}               OUT: Original Mles User Id
 * @param  channel {String}           OUT: Original Mles Channel
 */
 webWorker.onmessage = e.data["init", uid, channel]
```
### Reconnect message
```
/**
 * Reconnect Mles WebSocket connection after close
 *
 * @param  reconnect {String}         IN: command parameter "reconnect"
 * @param  data {String}              IN: data, null for "reconnect"
 * @param  uid {String}               IN: Mles User Id
 * @param  channel {String}           IN: Mles Channel
 */
 webWorker.postMessage[("reconnect", data, uid, channel)]
 ```
### Send message
```
/* Message type flags */
const MSGISFULL =       0x1;
const MSGISPRESENCE =  (0x1 << 1);
const MSGISIMAGE =     (0x1 << 2);
const MSGISMULTIPART = (0x1 << 3);
const MSGISFIRST =     (0x1 << 4);
const MSGISLAST =      (0x1 << 5);

/**
 * Send message over Mles WebSocket connection
 *
 * @param  send {String}              IN: command parameter "send"
 * @param  data {String}              IN: data to be sent
 * @param  uid {String}               IN: Mles User Id
 * @param  channel {String}           IN: Mles Channel
 * @param  randArray {Uint32Array}    IN: random array filled with input of length 8 x Uint32
 * @param  msgtype                    IN: message type flags in a single variable
 * @param  valueOfDate {Date}         IN: send time as Date
 */
 webWorker.postMessage[("send", data, uid, channel, randarr, msgtype, valueOfDate)]
 ```
### Data message receive
```
/**
 * Mles WebSocket RX data receive
 *
 * @param  data {String}               OUT: command parameter of receive "data"
 * @param  uid {String}                OUT: Original Mles User Id
 * @param  channel {String}            OUT: Original Mles Channel
 * @param  msgTimestamp {Date.valueOf} OUT: timestamp of the message in X format
 * @param  message {String}            OUT: received message
 * @param  msgtype                     OUT: message type flags in a single variable
 */
 webWorker.onmessage = e.data["data", uid, channel, msgTimestamp, message, msgtype]
```
### Close message
```
/**
 * Close message over Mles WebSocket connection
 *
 * @param  close {String}             IN: command parameter "close"
 * @param  data {String}              IN: data, null for close
 * @param  uid {String}               IN: Mles User Id
 * @param  channel {String}           IN: Mles Channel
 */
 webWorker.postMessage[("close", data, uid, channel)]
 ```
### Close message receive
```
/**
 * Mles WebSocket connection close receive after WebSocket closing
 *
 * @param  close {String}             OUT: command parameter of receive "close"
 * @param  uid {String}               OUT: Original Mles User Id
 * @param  channel {String}           OUT: Original Mles Channel
 */
 webWorker.onmessage = e.data["close", uid, channel]
```

## References

  1. The Transport Layer Security (TLS) Protocol Version 1.3, IETF RFC8446
  2. B. Schneier, 1994. Description of a New Variable-Length Key, 64-Bit Block Cipher (Blowfish).
  3. Rogaway, Wooding & Zhang, 2012. The Security of Ciphertext Stealing.
  4. Rivest, 1997. All-or-nothing transform.
  5. Aumasson, Neves, Wilcox-O’Hearn & Winnerlein, 2013. BLAKE2: simpler, smaller, fast as MD5.
  6. Kirill Nikitin, Ludovic Barman, Wouter Lueks, Matthew Underwood, Jean-Pierre Hubaux, Bryan Ford, 2019. Reducing Metadata Leakage from Encrypted Files and Communication with PURBs
  7. Colin Percival, 2009. Stronger key derivation via sequential memory-hard functions.
  8. Burmester, Desmedt, 1994. A secure and efficient conference key distribution system.
