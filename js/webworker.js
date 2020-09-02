/**
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 *
 * Copyright (c) 2019-2020 MlesTalk WebWorker developers
 */


importScripts('cbor.js', 'blake2s.js', 'blowfish.js', 'scrypt-async.js', 'bigint-mod-arith.js');

let gWebSocket;
let gMyAddr;
let gMyPort;
let gMyUid;
let gMyChannel;
let gChannelKey;
let gChanCrypt;
let gMsgCrypt;
const SCATTERSIZE = 15;
const ISFULL = 0x8000
const ISIMAGE = 0x4000;
const ISPRESENCE = 0x8000;
const ISPRESENCEACK = 0x4000; 
const ISMULTI = 0x4000; //reuse multi
const ISFIRST = 0x2000;
const ISLAST = 0x1000;
const BEGIN = new Date(Date.UTC(2018, 0, 1, 0, 0, 0));
const HMAC_LEN = 12;
const NONCE_LEN = 16;

const HDRLEN = 32;

/* Msg type flags */
const MSGISFULL =         0x1;
const MSGISPRESENCE =    (0x1 << 1);
const MSGISIMAGE =       (0x1 << 2);
const MSGISMULTIPART =   (0x1 << 3);
const MSGISFIRST =       (0x1 << 4);
const MSGISLAST =        (0x1 << 5);
const MSGISPRESENCEACK = (0x1 << 6);
const MSGPRESACKREQ =    (0x1 << 7);

const SCRYPT_SALTLEN = 32;
const SCRYPT_N = 32768;
const SCRYPT_R = 8;
const SCRYPT_P = 1;
const SCRYPT_DKLEN = 32;

const DH_GENERATOR = 2;
const DH_BITS = 512;
let gMyDhKey = {
	prime: BigInt(0),
	generator: BigInt(DH_GENERATOR),
	private: BigInt(0),
	public: BigInt(0),
	bd: BigInt(0),
	secret: BigInt(0),
	secretAcked: false,
	bdMsgCrypt: null,
	bdChannelKey: null,
	prevBdMsgCrypt: null,
	prevBdChannelKey: null,
	fsInformed: false
};

let gDhDb = {};
let gBdDb = {};
let gBdAckDb = {};

function scatterU16(rvalU32, valU32, valU16) {
	//check first which bits to use
	let tbit = new Uint32Array(1);
	let bit = new Uint32Array(1);
	let numofones = 0;
	let isOnes = true;
	for (let i = 31; i >= 0; i--) {
		bit[0] = (rvalU32 & (1 << i)) >> i;
		if (bit[0] > 0) {
			numofones++;
		}
	}
	let slot = SCATTERSIZE;
	if (numofones <= slot)
		isOnes = false;
	for (let i = 31; i >= 0; i--) {
		bit[0] = (rvalU32 & (1 << i)) >> i;
		if ((isOnes && bit[0] > 0) || (false == isOnes && 0 == bit[0])) {
			//apply setting to next item
			tbit[0] = (valU16 & (1 << slot)) >> slot;
			if (tbit[0] > 0) {
				valU32 |= (1 << i);
			}
			else {
				valU32 &= ~(1 << i);
			}
			slot--;
			if (slot < 0)
				break;
		}
	}
	return valU32;
}

function unscatterU16(rvalU32, svalU32) {
	//check first which bits to use
	let valU16 = new Uint32Array(1);
	let sbit = new Uint32Array(1);
	let bit = new Uint32Array(1);
	let numofones = 0;
	let isOnes = true;
	for (let i = 31; i >= 0; i--) {
		bit[0] = (rvalU32 & (1 << i)) >> i;
		if (bit[0] > 0) {
			numofones++;
		}
	}
	let slot = SCATTERSIZE;
	if (numofones <= slot)
		isOnes = false;
	for (let i = 31; i >= 0; i--) {
		bit[0] = (rvalU32 & (1 << i)) >> i;
		if ((isOnes && bit[0] > 0) || (false == isOnes && 0 == bit[0])) {
			sbit[0] = (svalU32 & (1 << i)) >> i;
			if (sbit[0] > 0)
				valU16[0] |= (1 << slot);
			slot--;
			if (slot < 0)
				break;
		}
	}
	return valU16[0];
}

function createTimestamp(valueofdate, weekstamp) {
	let begin = BEGIN;
	let this_week = new Date(begin.valueOf() + weekstamp * 1000 * 60 * 60 * 24 * 7);
	let timestamp = parseInt((valueofdate - this_week) / 1000 / 60);
	return timestamp;
}

function createWeekstamp(valueofdate) {
	let begin = BEGIN;
	let now = new Date(valueofdate);
	let weekstamp = parseInt((now - begin) / 1000 / 60 / 60 / 24 / 7);
	return weekstamp;
}

function readTimestamp(timestamp, weekstamp) {
	let begin = BEGIN;
	let weeks = new Date(begin.valueOf() + weekstamp * 1000 * 60 * 60 * 24 * 7);
	let extension = timestamp * 1000 * 60;
	let time = new Date(weeks.valueOf() + extension);
	return time;
}

function isEqualHmacs(hmac, rhmac) {
	let mac1 = new BLAKE2s(HMAC_LEN);
	let mac2 = new BLAKE2s(HMAC_LEN);

	mac1.update(hmac);
	mac2.update(rhmac);

	let hmac1 = mac1.digest();
	let hmac2 = mac2.digest();

	for (let i = 0; i < hmac1.byteLength; i++) {
		if (hmac1[i] != hmac2[i]) {
			return false;
		}
	}
	return true;
}

function nonce2u8arr(nonce) {
	let nonceu8 = new Uint8Array(NONCE_LEN);
	nonceu8[0] = nonce[0] >> 24;
	nonceu8[1] = nonce[0] >> 16 & 0xff;
	nonceu8[2] = nonce[0] >> 8 & 0xff;
	nonceu8[3] = nonce[0] & 0xff;
	nonceu8[4] = nonce[1] >> 24;
	nonceu8[5] = nonce[1] >> 16 & 0xff;
	nonceu8[6] = nonce[1] >> 8 & 0xff;
	nonceu8[7] = nonce[1] & 0xff;
	nonceu8[8] = nonce[2] >> 24;
	nonceu8[9] = nonce[2] >> 16 & 0xff;
	nonceu8[10] = nonce[2] >> 8 & 0xff;
	nonceu8[11] = nonce[2] & 0xff;
	nonceu8[12] = nonce[3] >> 24;
	nonceu8[13] = nonce[3] >> 16 & 0xff;
	nonceu8[14] = nonce[3] >> 8 & 0xff;
	nonceu8[15] = nonce[3] & 0xff;
	return nonceu8;
}

function u8arr2nonce(noncem) {
	let nonce = new Uint32Array(4);
	nonce[0] = noncem[0] << 24 | noncem[1] << 16 | noncem[2] << 8 | noncem[3];
	nonce[1] = noncem[4] << 24 | noncem[5] << 16 | noncem[6] << 8 | noncem[7];
	return nonce;
}

function load32(a, i) {
	return (a[i + 0] & 0xff) | ((a[i + 1] & 0xff) << 8) |
		((a[i + 2] & 0xff) << 16) | ((a[i + 3] & 0xff) << 24);
}

function store32(a, i, val) {
	a[i + 0] = val & 0xff;
	a[i + 1] = (val & 0xff00) >> 8;
	a[i + 2] = (val & 0xff0000) >> 16;
	a[i + 3] = (val & 0xff000000) >> 24;
	return a;
}

function StringToUint8(str) {
	let arr = new Uint8Array(str.length);
	let len = str.length;
	for (let i = 0; i < len; i++) {
		arr[i] = str.charCodeAt(i);
	}
	return arr;
}

function Uint8ToString(arr) {
	let str = new String('');
	for (let i = 0; i < arr.length; i++) {
		str += String.fromCharCode(arr[i]);
	};
	return str;
}

function initBd(myuid) {
	gBdDb = {};
	gBdAckDb = {};
	gMyDhKey.secret = BigInt(0);
	gMyDhKey.secretAcked = false;
	gMyDhKey.bdMsgCrypt = null;
}

function initDhBd(myuid) {
	gDhDb = {};
	gBdDb = {};
	gBdAckDb = {};
	if (gMyDhKey.public) {
		gDhDb[myuid] = gMyDhKey.public;
	}
	gMyDhKey.secret = BigInt(0);
	gMyDhKey.secretAcked = false;
	gMyDhKey.bdMsgCrypt = null;
}

function processBd(uid, msgtype, message) {
	const myuid = gChanCrypt.trimZeros(gChanCrypt.decrypt(atob(gMyUid)));
	if(uid == myuid) {  //received own message, init due to resyncing
		initDhBd(myuid);
	}
	else if (message.length == 64 || message.length == 65 || message.length == 66 || message.length == 128 || message.length == 129) {
		//console.log("Got " + uid + " public+bd key, len " + message.length);
		let init = false;

		if (message.length == 64 || message.length == 65 || message.length == 128) {
			if (!(msgtype & MSGISPRESENCEACK)) {
				msgtype |= MSGPRESACKREQ; // inform upper layer about presence ack requirement
			}
			if (gMyDhKey.secretAcked) {
				//console.log("!!! skey invalidated in short message !!!");
				initDhBd(myuid);
				init = true;
			}
		}

		let pub = buf2bn(StringToUint8(message.substring(0, 64)));
		if (null == gDhDb[uid]) {
			gDhDb[uid] = pub;
		}
		else if (gDhDb[uid] != pub) {
			initDhBd(myuid);
			//console.log("!!! skey invalidated in mismatching dh!!!");
			gDhDb[uid] = pub;
			init = true;
		}
		else if (message.length == 64 && gDhDb[uid] && gBdDb[uid]) {
			initDhBd(myuid);
			//console.log("!!! skey invalidated in short message as with existing bd!!!");
			gDhDb[uid] = pub;
			init = true;
		}
		else if(!init) {
			//calculate bd key
			let prevkey = null;
			let nextkey = null;
			let index = 0;
			let pubcnt = 0;
			let dhdb_sorted = Object.fromEntries(Object.entries(gDhDb).sort());
			let keys = [];
			for (let userid in dhdb_sorted) {
				if (userid == myuid) {
					index = pubcnt;
				}
				keys.push(gDhDb[userid]);
				pubcnt++;
			}

			const len = keys.length;
			if (index == 0) {
				prevkey = keys[len - 1];
				nextkey = keys[index + 1];
			}
			else if (index == len - 1) {
				prevkey = keys[index - 1];
				nextkey = keys[0];
			}
			else {
				prevkey = keys[index - 1];
				nextkey = keys[index + 1];
			}
			if (prevkey && nextkey) {
				let bd = nextkey * modInv(prevkey, gMyDhKey.prime) % gMyDhKey.prime;
				gMyDhKey.bd = modPow(bd, gMyDhKey.private, gMyDhKey.prime);
				gBdDb[myuid] = gMyDhKey.bd;
			}

			if (message.length == 128 || message.length == 65 || message.length == 66 || message.length == 129) {
				let len;
				if (message.length >= 128)
					len = 128;
				else
					len = 65;
				let bd = buf2bn(StringToUint8(message.substring(64, len)));

				if (gBdDb[uid] != null && gBdDb[uid] != bd) {
					//start again
					initBd(myuid);
					//console.log("!!! skey invalidated in mismatching bd !!!");
					init = true;
				}
				else if (pubcnt > 2 && bd == BigInt(1) || pubcnt == 2 && bd != BigInt(1)) {
					initBd(myuid);
					//console.log("!!! skey invalidated in mismatching bd length!!! pubcnt " + pubcnt + " bd " + bd.toString(16));
					init = true;
				}
				else if (gBdDb[uid] == bd) {
					//BD matches, do nothing
				}
				else {
					gBdDb[uid] = bd;

					let bdcnt = 0;
					let xkeys = [];
					let bddb_sorted = Object.fromEntries(Object.entries(gBdDb).sort());
					for (let userid in bddb_sorted) {
						if (userid == myuid) {
							index = bdcnt;
						}
						xkeys.push(gBdDb[userid]);
						bdcnt++;
					}

					if (bdcnt == pubcnt) {
						//calculate secret key
						let len = BigInt(xkeys.length);
						let skey = modPow(prevkey, len * gMyDhKey.private, gMyDhKey.prime);
						let sub = BigInt(1);
						for (let i = 0; i < xkeys.length; i++) {
							let base = xkeys[(i + index) % xkeys.length];
							let xPow = modPow(base, len - sub, gMyDhKey.prime);
							skey *= xPow;
							sub++;
						}
						skey %= gMyDhKey.prime;
						//console.log("!!! My skey " + skey.toString(16) + " !!!");
						gMyDhKey.secret = skey;

						let rnd = new BLAKE2s(32);
						rnd.update(gChannelKey);
						rnd.update(StringToUint8(gMyDhKey.secret.toString(16)));

						gMyDhKey.bdChannelKey = createChannelKey(rnd.digest());
						let key = createMessageKey(rnd.digest());
						let aontkey = createMessageAontKey(rnd.digest());

						gMyDhKey.bdMsgCrypt = createMessageCrypt(key, aontkey);
						//console.log("Created key msg crypt! " + key)

						rnd = '';
						key = '';
						aontkey = '';
					}
				}
				//if bd handling fails, ignore large handling
				if (!init && message.length == 66 || message.length == 129) {
					if (gMyDhKey.secretAcked) {
						//do nothing, already acked
					}
					else {
						//check first that pub and bd are ok
						if (gDhDb[uid] && gBdDb[uid]) {
							gBdAckDb[uid] = true;
							let pubcnt = Object.keys(gDhDb).length;
							let bdcnt = Object.keys(gBdDb).length;
							let ackcnt = Object.keys(gBdAckDb).length;
							//ack received from everyone else?
							//console.log("Ackcnt " + ackcnt + " pubcnt " + pubcnt + " bdcnt " + bdcnt);
							if (pubcnt == bdcnt && ackcnt == pubcnt &&
								(message.length == 66 && pubcnt == 2 ||
									message.length == 129 && pubcnt > 2)) {

								//console.log("Ack count matches to pub&bdcnt, enabling send encryption!");
								gMyDhKey.secretAcked = true;
							}
						}
						else {
							//start again
							initDhBd(myuid);
							//console.log("!!! bds invalidated in ack !!!");
							gDhDb[uid] = pub;
						}
					}
				}
			}
		}
	}
}

function processOnMessageData(msg) {
	//sanity
	if (msg.message.byteLength <= NONCE_LEN || msg.message.byteLength > 0xffffff) {
		return;
	}

	let fsEnabled = false;
	let noncem = msg.message.slice(0, NONCE_LEN);
	let arr = msg.message.slice(NONCE_LEN, msg.message.byteLength - HMAC_LEN);
	let hmac = msg.message.slice(msg.message.byteLength - HMAC_LEN, msg.message.byteLength)
	let message = Uint8ToString(arr);

	//verify first hmac
	let hmacarr = new Uint8Array(noncem.byteLength + arr.byteLength);
	hmacarr.set(noncem, 0);
	hmacarr.set(arr, noncem.byteLength);
	let hmacok = false;
	let crypt; //selected crypt object

	//try all three options
	if(gMyDhKey.bdMsgCrypt) {
		let blakehmac = new BLAKE2s(HMAC_LEN);
		blakehmac.update(gMyDhKey.bdChannelKey);
		blakehmac.update(hmacarr);
		let rhmac = blakehmac.digest();
		if (true == isEqualHmacs(hmac, rhmac)) {
			hmacok = true;
			crypt = gMyDhKey.bdMsgCrypt;
			fsEnabled = true;
		}
	}
	if(!hmacok && gMyDhKey.prevBdMsgCrypt) {
		let blakehmac = new BLAKE2s(HMAC_LEN);
		blakehmac.update(gMyDhKey.prevBdChannelKey);
		blakehmac.update(hmacarr);
		let rhmac = blakehmac.digest();
		if (true == isEqualHmacs(hmac, rhmac)) {
			hmacok = true;
			crypt = gMyDhKey.prevBdMsgCrypt;
			fsEnabled = true;
		}
	}
	if(!hmacok) {
		let blakehmac = new BLAKE2s(HMAC_LEN)
		blakehmac.update(gChannelKey);
		blakehmac.update(hmacarr);
		let rhmac = blakehmac.digest();
		if (false == isEqualHmacs(hmac, rhmac)) {
			return;
		}
		if(gMyDhKey.fsInformed) {
			processOnForwardSecrecyOff();
			gMyDhKey.fsInformed = false;
		}
		crypt = gMsgCrypt;
	}

	let nonce = u8arr2nonce(noncem);
	let iv = nonce.slice(0, 2);

	let uid = gChanCrypt.trimZeros(gChanCrypt.decrypt(atob(msg.uid)));
	let channel = gChanCrypt.trimZeros(gChanCrypt.decrypt(atob(msg.channel)));
	let decrypted = crypt.decrypt(message, iv);

	if (decrypted.length < HDRLEN) {
		return;
	}

	let versizestr = decrypted.slice(0, 8);
	let varray = crypt.split64by32(versizestr);
	const msgsz = unscatterU16(varray[0], varray[1]);

	let keysizestr = decrypted.slice(8, 16);
	let karray = crypt.split64by32(keysizestr);
	let keysz = unscatterU16(karray[0], karray[1]);

	//let padsz = decrypted.length - msgsz - keysz;
	//console.log("RX: Msgsize " + msgsz + " Keysz " + keysz + " Pad size " + padsz);

	let timestring = decrypted.slice(16, 24);
	let rarray = crypt.split64by32(timestring);
	let timeU16 = unscatterU16(rarray[0], rarray[1]);
	let weekstring = decrypted.slice(24, HDRLEN);
	let warray = crypt.split64by32(weekstring);
	let weekU16 = unscatterU16(warray[0], warray[1]);
	let msgDate = readTimestamp(timeU16 & ~(ISFULL | ISIMAGE), weekU16 & ~(ISPRESENCE | ISMULTI | ISFIRST | ISLAST));

	message = decrypted.slice(HDRLEN, msgsz);

	let msgtype = 0;
	if (timeU16 & ISFULL)
		msgtype |= MSGISFULL;
	if (timeU16 & ISIMAGE)
		msgtype |= MSGISIMAGE;
	if (weekU16 & ISPRESENCE) {
		msgtype |= MSGISPRESENCE;
		if (weekU16 & ISPRESENCEACK)
			msgtype |= MSGISPRESENCEACK;
	}
	if (!(weekU16 & ISPRESENCE) && weekU16 & ISMULTI)
		msgtype |= MSGISMULTIPART;
	if (weekU16 & ISFIRST)
		msgtype |= MSGISFIRST;
	if (weekU16 & ISLAST)
		msgtype |= MSGISLAST;

	if(keysz > 0) {
		const keystr = decrypted.slice(msgsz, msgsz+keysz);
		processBd(uid, msgtype, keystr);
	}

	postMessage(["data", uid, channel, msgDate.valueOf(), message, msgtype, fsEnabled]);
}

function msgDecode(data) {
	try {
		return CBOR.decode(data);
	} catch (err) {
		return null;
	}
}

function msgEncode(obj) {
	try {
		return CBOR.encode(obj);
	} catch (err) {
		return null;
	}
}

function processOnClose() {
	gWebSocket.close();
	let uid = gChanCrypt.trimZeros(gChanCrypt.decrypt(atob(gMyUid)));
	let channel = gChanCrypt.trimZeros(gChanCrypt.decrypt(atob(gMyChannel)));
	postMessage(["close", uid, channel, gMyUid, gMyChannel]);
}

function processOnOpen() {
	let uid = gChanCrypt.trimZeros(gChanCrypt.decrypt(atob(gMyUid)));
	let channel = gChanCrypt.trimZeros(gChanCrypt.decrypt(atob(gMyChannel)));
	postMessage(["init", uid, channel, gMyUid, gMyChannel]);
}

function processOnForwardSecrecy(bdKey) {
	let uid = gChanCrypt.trimZeros(gChanCrypt.decrypt(atob(gMyUid)));
	let channel = gChanCrypt.trimZeros(gChanCrypt.decrypt(atob(gMyChannel)));
	postMessage(["forwardsecrecy", uid, channel, gMyUid, gMyChannel, bdKey.toString(16)]);
}

function processOnForwardSecrecyOff() {
	let uid = gChanCrypt.trimZeros(gChanCrypt.decrypt(atob(gMyUid)));
	let channel = gChanCrypt.trimZeros(gChanCrypt.decrypt(atob(gMyChannel)));
	postMessage(["forwardsecrecyoff", uid, channel, gMyUid, gMyChannel]);
}


function openSocket(gMyPort, gMyAddr) {
	if (gWebSocket !== undefined && gWebSocket.readyState == WebSocket.OPEN) {
		return;
	}

	gWebSocket = new WebSocket("wss://" + gMyAddr + ":" + gMyPort, "mles-websocket");
	gWebSocket.binaryType = "arraybuffer";
	gWebSocket.onopen = function (event) {
		let ret = processOnOpen();
		if(ret < 0)
			console.log("Process on open failed: " + ret);

	};

	gWebSocket.onmessage = function (event) {
		if (event.data) {
			let msg = msgDecode(event.data);
			if(!msg)
				return;

			let ret = processOnMessageData(msg);
			if(ret < 0)
				console.log("Process on message data failed: " + ret);
		}
	};

	gWebSocket.onclose = function (event) {
		let ret = processOnClose();
		if(ret < 0)
			console.log("Process on close failed: " + ret)
	};
}

function createChannelKey(passwd) {
	let round = new BLAKE2s(32);
	round.update(passwd);
	let blakecb = new BLAKE2s(7); //56-bits max key len
	blakecb.update(round.digest());
	return blakecb.digest();
}

function createChannelAontKey(passwd) {
	let round = new BLAKE2s(32);
	round.update(passwd);
	round.update(passwd);
	let blakeaontecb = new BLAKE2s(8); //aont key len
	blakeaontecb.update(round.digest());
	return blakeaontecb.digest();
}

function createMessageKey(passwd) {
	let blakecbc = new BLAKE2s(7); //56-bits max key len
	blakecbc.update(passwd);
	return blakecbc.digest();
}

function createMessageAontKey(passwd) {
	let round = new BLAKE2s(32);
	round.update(passwd);
	round.update(passwd);
	round.update(passwd);
	let blakeaontcbc = new BLAKE2s(8); //aont key len
	blakeaontcbc.update(round.digest());
	return blakeaontcbc.digest();
}

function createChannelCrypt(channelKey, channelAontKey) {
	return new Blowfish(channelKey, channelAontKey);
}

function createMessageCrypt(messageKey, messageAontKey) {
	return new Blowfish(messageKey, messageAontKey, "cbc");
}

function checkPrime(candidate) {
	return isPrime(fromBuffer(candidate))
}

function isPrime(candidate) {
	// Testing if a number is a probable prime (Miller-Rabin)
	const number = BigInt(candidate)
	const isPrime = _isProbablyPrime(number, 6)
	//if(isPrime) {
  	//	console.log(number.toString(16) +  " is prime")
	//}
	return isPrime;
}

function getDhPrime(bits, passwd) {
	let rounds = 0;
	let sprime = 0;

	if(bits <= 0 || bits % 512 || bits > 4096)
		throw new RangeError("Invalid key bits" + bits);

	let rnd = new BLAKE2s(32);
	rnd.update(passwd);
	let seed = rnd.digest();
	let dhhprime = new BLAKE2s(32, seed);
	let dhlprime = new BLAKE2s(32, dhhprime.digest());
	let aPrime = false;
	let dhprime = new Uint8Array(bits/8);

	while (false == aPrime) {
		let cnt = 0;
		while(cnt < bits/8) {
			dhhprime = new BLAKE2s(32, dhlprime.digest());
			dhlprime = new BLAKE2s(32, dhhprime.digest());

			let hival = dhhprime.digest();
			for (let i = 0; i < 32; i++) {
				dhprime[cnt++] = hival[i];
			}
			let loval = dhlprime.digest();
			for (let i = 0; i < 32; i++) {
				dhprime[cnt++] = loval[i];
			}
		}
		dhprime[0] |= 0x80;
		dhprime[bits / 8 - 1] |= 0x1;
		aPrime = checkPrime(dhprime);
		if (aPrime) {
			sprime = buf2bn(dhprime);
			//qprime = fromBuffer(dhprime);
			//sprime = BigInt(2)*qprime-BigInt(1);
			//aPrime = isPrime(sprime);
		}
		rounds++;
	} 
	return sprime;
}

function bn2buf(bn) {
	var hex = BigInt(bn).toString(16);
	if (hex.length % 2) { hex = '0' + hex; }
  
	var len = hex.length / 2;
	var u8 = new Uint8Array(len);
  
	var i = 0;
	var j = 0;
	while (i < len) {
	  u8[i] = parseInt(hex.slice(j, j+2), 16);
	  i += 1;
	  j += 2;
	}
  
	return u8;
  }

function buf2bn(buf) {
	var hex = [];
	u8 = Uint8Array.from(buf);
  
	u8.forEach(function (i) {
	  var h = i.toString(16);
	  if (h.length % 2) { h = '0' + h; }
	  hex.push(h);
	});
  
	return BigInt('0x' + hex.join(''));
}

const MAXRND = 0x3ff;
/* Padmé: https://lbarman.ch/blog/padme/ with random component */
function padme(msgsize, rnd) {
	const L = msgsize + (rnd & ~msgsize & MAXRND);
	const E = Math.floor(Math.log2(L));
	const S = Math.floor(Math.log2(E))+1;
	const lastBits = E-S;
	const bitMask = 2 ** lastBits - 1;
	return (L + bitMask) & ~bitMask;
}

onmessage = function (e) {
	let cmd = e.data[0];
	let data = e.data[1];

	switch (cmd) {
		case "init":
			{
				gMyAddr = e.data[2];
				gMyPort = e.data[3];
				let uid = e.data[4];
				let channel = e.data[5];
				let passwd = StringToUint8(e.data[6]);
				let isEncryptedChannel = e.data[7];
				let prevBdKey = e.data[8];

				//salt
				let salt = new BLAKE2s(SCRYPT_SALTLEN);
				salt.update(passwd);
				salt.update(StringToUint8('salty-mlestalk'));

				//scrypt
				scrypt(passwd, salt.digest(), {
					N: SCRYPT_N,
					r: SCRYPT_R,
					p: SCRYPT_P,
					dkLen: SCRYPT_DKLEN,
					encoding: 'binary'
				}, function(derivedKey) {
					passwd = derivedKey;
				});

				let private = new Uint8Array(DH_BITS/8);
				self.crypto.getRandomValues(private);

				gMyDhKey.prime = getDhPrime(DH_BITS, passwd);
				gMyDhKey.private = buf2bn(private);
				gMyDhKey.public = modPow(gMyDhKey.generator, gMyDhKey.private, gMyDhKey.prime);
				//update database
				gDhDb[uid] = gMyDhKey.public;

				gChannelKey = createChannelKey(passwd);
				if(prevBdKey) {
					let rnd = new BLAKE2s(32);
					rnd.update(gChannelKey);
					rnd.update(StringToUint8(prevBdKey));

					gMyDhKey.prevBdChannelKey = createChannelKey(rnd.digest());
					let key = createMessageKey(rnd.digest());
					let aontkey = createMessageAontKey(rnd.digest());
					gMyDhKey.prevBdMsgCrypt = createMessageCrypt(key, aontkey);
				}

				let channelAontKey = createChannelAontKey(passwd);
				let messageKey = createMessageKey(passwd);
				let messageAontKey = createMessageAontKey(passwd)

				gChanCrypt = createChannelCrypt(gChannelKey, channelAontKey);	
				gMsgCrypt = createMessageCrypt(messageKey, messageAontKey);
				gMyUid = btoa(gChanCrypt.encrypt(uid));

				//wipe unused
				salt = "";
				passwd = "";
				channelAontKey = "";
				messageKey = "";
				messageAontKey = "";

				let bfchannel;
				if (!isEncryptedChannel) {
					bfchannel = gChanCrypt.encrypt(channel);
					gMyChannel = btoa(bfchannel);
				}
				else {
					gMyChannel = channel;
				}
				openSocket(gMyPort, gMyAddr);
			}
			break;
		case "reconnect":
			{
				let uid = e.data[2];
				let channel = e.data[3];
				let isEncryptedChannel = e.data[4];

				uid = btoa(gChanCrypt.encrypt(uid));
				if (!isEncryptedChannel) {
					bfchannel = gChanCrypt.encrypt(channel);
					channel = btoa(bfchannel);
				}
				// verify that we have already opened the channel earlier
				if (gMyUid === uid && gMyChannel === channel) {
					openSocket(gMyPort, gMyAddr);
				}
			}
			break;
		case "send":
			{
				let uid = e.data[2];
				let channel = e.data[3];
				let isEncryptedChannel = e.data[4];
				let msgtype = e.data[5];
				let valueofdate = e.data[6];
				let keysz = 0;

				let randarr = new Uint32Array(13);
				self.crypto.getRandomValues(randarr);

				let iv = randarr.slice(0, 2);
				let nonce = randarr.slice(0, 4);
				let rarray = randarr.slice(4);

				if (isEncryptedChannel) {
					channel = gChanCrypt.trimZeros(gChanCrypt.decrypt(atob(channel)));
				}

				let weekstamp = createWeekstamp(valueofdate);
				let timestamp = createTimestamp(valueofdate, weekstamp);
				if (msgtype & MSGISFULL)
					timestamp |= ISFULL;

				if (msgtype & MSGISIMAGE) {
					timestamp |= ISIMAGE;
				}
				if (msgtype & MSGISPRESENCE) {
					weekstamp |= ISPRESENCE;
					if (msgtype & MSGISPRESENCEACK)
						weekstamp |= ISPRESENCEACK;
				}

				if (!(msgtype & MSGISPRESENCE) && msgtype & MSGISMULTIPART) {
					weekstamp |= ISMULTI;
					if (msgtype & MSGISFIRST) {
						weekstamp |= ISFIRST;
					}
					if (msgtype & MSGISLAST) {
						weekstamp |= ISLAST;
					}
				}

				const msgsz = data.length + HDRLEN;

				//add public key, if it exists
				if (gMyDhKey.public) {
					let pub = Uint8ToString(bn2buf(gMyDhKey.public));
					keysz += pub.length;
					data += pub;
				}
				//add BD key, if it exists
				if (gMyDhKey.bd) {
					let bd = Uint8ToString(bn2buf(gMyDhKey.bd));
					keysz += bd.length;
					data += bd;
					let pubcnt = Object.keys(gDhDb).length;
					let bdcnt = Object.keys(gBdDb).length;
					//console.log("During send pubcnt " + pubcnt + " bdcnt " + bdcnt)
					if (pubcnt == bdcnt && gMyDhKey.secret != BigInt(0)) {
						let bd = Uint8ToString(bn2buf(BigInt(1)));
						keysz += bd.length;
						data += bd;
						if (gBdAckDb[uid] == null) {
							//console.log("Adding self to bdack db");
							gBdAckDb[uid] = true;
						}
					}
				}



				//version and msg size
				let hval = scatterU16(rarray[0], rarray[1], msgsz);
				rarray[1] = hval;
				//key size
				let kval = scatterU16(rarray[2], rarray[3], keysz);
				rarray[3] = kval;
				//time vals
				let sval = scatterU16(rarray[4], rarray[5], timestamp);
				rarray[5] = sval;
				sval = scatterU16(rarray[6], rarray[7], weekstamp);
				rarray[7] = sval;

				let newmessage;
				let encrypted;
				let crypt;
				let channel_key;
				if(gMyDhKey.bdMsgCrypt && gMyDhKey.secret && gMyDhKey.secretAcked) {
					if(!(msgtype & MSGISPRESENCE) && !gMyDhKey.fsInformed) {
						processOnForwardSecrecy(gMyDhKey.secret);
						gMyDhKey.fsInformed = true;
					}
					crypt = gMyDhKey.bdMsgCrypt;
					channel_key = gMyDhKey.bdChannelKey;
				}
				else {
					crypt = gMsgCrypt;
					channel_key = gChannelKey;
				}

				//version, size and key values
				newmessage = crypt.num2block32(rarray[0]) + crypt.num2block32(rarray[1]) +
							crypt.num2block32(rarray[2]) + crypt.num2block32(rarray[3]);
				//time values
				newmessage += crypt.num2block32(rarray[4]) + crypt.num2block32(rarray[5]) +
							crypt.num2block32(rarray[6]) + crypt.num2block32(rarray[7]);
				//message itself
				newmessage += data;

				const msglen = msgsz + keysz;
				//padmé padding
				const padsz = padme(msglen, rarray[8]) - msglen;
				//console.log("TX: Msgsize " + msgsz + " padding sz " + padsz + " keysz " + keysz)
				if(padsz > 0) {
					newmessage += Uint8ToString(randBytesSync(padsz));
				}

				encrypted = crypt.encrypt(newmessage, iv);
				
				let noncearr = nonce2u8arr(nonce);
				let arr = StringToUint8(encrypted);

				// calculate hmac
				let hmacarr = new Uint8Array(noncearr.byteLength + arr.byteLength);
				hmacarr.set(noncearr, 0);
				hmacarr.set(arr, noncearr.byteLength);

				let blakehmac = new BLAKE2s(HMAC_LEN);
				blakehmac.update(channel_key);
				blakehmac.update(hmacarr);
				let hmac = blakehmac.digest();

				let newarr = new Uint8Array(noncearr.byteLength + arr.byteLength + hmac.byteLength);
				newarr.set(noncearr, 0);
				newarr.set(arr, noncearr.byteLength);
				newarr.set(hmac, noncearr.byteLength + arr.byteLength);
				let obj = {
					uid: btoa(gChanCrypt.encrypt(uid)),
					channel: btoa(gChanCrypt.encrypt(channel)),
					message: newarr
				};
				let encodedMsg = msgEncode(obj);
				if(!encodedMsg)
					break;
				try {
					gWebSocket.send(encodedMsg);
				} catch (err) {
					break;
				}
				postMessage(["send", uid, channel, msgtype & MSGISMULTIPART ? true : false]);


			}
			break;
		case "close":
			{
				//let uid = e.data[2];
				//let channel = e.data[3];
				//let isEncryptedChannel = e.data[4];
				gWebSocket.close();
			}
			break;
	}
}
