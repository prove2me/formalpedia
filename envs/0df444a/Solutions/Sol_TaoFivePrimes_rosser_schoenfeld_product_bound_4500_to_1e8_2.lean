-- Prove2me | solution 2 for TaoFivePrimes.rosser_schoenfeld_product_bound_4500_to_1e8
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-09-23T18:30:02.960595+00:00
-- url     : https://prove2.me/submissions/891aecdd-2026-4fbb-9bf7-a2b4a368f347

import Mathlib.Data.Nat.Sqrt
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.Ring.GeomSum
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Nat.ModEq

set_option autoImplicit false
set_option Elab.async false

-- Source: Solutions/RosserCompute.lean
/-! Pure natural-number computations for the Rosser--Schoenfeld certificate.
Numerical certificate modules import only this file; real analysis and
correctness proofs remain in the separate proof modules. -/

namespace RosserBitSieve


def periodicMask (d count : ℕ) : ℕ :=
  (2 ^ (d * count) - 1) / (2 ^ d - 1)

def divisorMask (a len d : ℕ) : ℕ :=
  periodicMask d ((len + d - 1) / d) * 2 ^ ((d - a % d) % d)

def compositeMask (divisors : List ℕ) (a len : ℕ) : ℕ :=
  divisors.foldl (fun mask d => mask ||| divisorMask a len d) 0

def candidateMask (divisors : List ℕ) (a len : ℕ) : ℕ :=
  (2 ^ len - 1) ^^^ (compositeMask divisors a len % 2 ^ len)

/-- Enumerate a bit interval by halving it, skipping empty subtrees. -/
def enumBits : ℕ → ℕ → ℕ → List ℕ
  | 0, start, mask => if mask % 2 == 1 then [start] else []
  | depth + 1, start, mask =>
    if mask == 0 then [] else
    let half := 2 ^ depth
    enumBits depth start (mask % 2 ^ half) ++
      enumBits depth (start + half) (mask / 2 ^ half)

def offsets (divisors : List ℕ) (depth a len : ℕ) : List ℕ :=
  enumBits depth 0 (candidateMask divisors a len)

/-- Reuse one sieve mask for many short blocks. Offsets here start at one. -/
def windowOffsets (depth mask shift len : ℕ) : List ℕ :=
  (enumBits depth 0 (mask / 2 ^ shift % 2 ^ len)).map (· + 1)

end RosserBitSieve

namespace AlternativeProductMoments


def firstMoment (ds : List ℕ) : ℕ := ds.sum

def secondMoment (ds : List ℕ) : ℕ := (ds.map (fun (d : ℕ) => d ^ 2)).sum

def lowerNumerator (a : ℕ) (ds : List ℕ) : ℕ :=
  ds.length * a - firstMoment ds

def upperNumerator (a : ℕ) (ds : List ℕ) : ℕ :=
  ds.length * a ^ 2 - a * firstMoment ds + secondMoment ds

def pairNumerator (a : ℕ) (ds : List ℕ) : ℕ :=
  lowerNumerator a ds ^ 2 - ds.length * a ^ 2

def factorNumerator (a : ℕ) (ds : List ℕ) : ℕ :=
  (a ^ 3 - upperNumerator a ds) * (2 * a ^ 4 + pairNumerator a ds)

def factorDenominator (a : ℕ) : ℕ := 2 * a ^ 7

/-- One downward-rounded update for a whole candidate block. -/
def momentStep (v a : ℕ) (ds : List ℕ) : ℕ :=
  v * factorNumerator a ds / factorDenominator a

end AlternativeProductMoments

namespace RosserBitMoments

open RosserBitSieve AlternativeProductMoments

@[ext] structure Moments where
  count : ℕ
  first : ℕ
  second : ℕ
  deriving DecidableEq, Repr

def moments (ds : List ℕ) : Moments :=
  ⟨ds.length, ds.sum, (ds.map (fun (d : ℕ) => d ^ 2)).sum⟩

def merge (s t : Moments) : Moments :=
  ⟨s.count + t.count, s.first + t.first, s.second + t.second⟩

def translate (offset : ℕ) (s : Moments) : Moments :=
  ⟨s.count, s.first + offset * s.count,
    s.second + 2 * offset * s.first + offset ^ 2 * s.count⟩

def packedTable : ℕ := 18472300896970103792108295030754343311462210589054640814582099618958825816112921765637552819554960025580043253363337196071510397018042133440073613070599528214959555081087759177994513208873881398958301422300628985358844335629703824674989009933744813385983504668349668413339407645329016240118311102009327559169919361752210702429893649728293932236557803946372391347786424282478245140012004923246019750498074272682481869124019625063780294997972415480522849467413156748308598193741959980512364680419185912142662080168720543223372130422252685000667222028691552391144914476582653820543415241442522565567827850971540414084963023662461454138479593909733901640282571543659792227281002640358593405226625400471739963595439608037996346958976031522266509217418626068981435972643586956604265934825153588078474541062083601584565110669452202573339800164169103872550900181154149463648375952255080306757167758906906382736410940812007907700484645358916007966298027371443379797534272791198303638115965305949698405311795153919406852986359475633446763175764573556098103639551525890208319167226087125167594382204144161586295123540456912808096572570872821701693833155843103822148960692081668132802646373741121271338591023149542977379459365527447593127745781442122554270427974619422849735484296339832731170084457029930842499657049873841177855047761694425403274812125429077333590092198933962090340380251846202809362383975418479306463890842278375332614640909801129604954946001702919968537917515644728884667828251078535570507012846902588218779713741378512607411980300476879133811456575684021346503785234617675182982977540462331832399895301441454472653688500254658691068207975085644854631617042755709815233293970628383901959051862306499230180026929443703650068362443283922131960509713762221413633617444652901862094089062362383582693974422591379320268703353694406511098994725224448

def byteMoments (byte : ℕ) : Moments :=
  if byte == 0 then ⟨0, 0, 0⟩ else
  if byte &&& (byte - 1) == 0 then
    let bit := Nat.log2 byte
    ⟨1, bit, bit ^ 2⟩
  else
    let word := packedTable / 2 ^ (24 * byte) % 2 ^ 24
    ⟨word % 256, word / 256 % 256, word / 65536 % 256⟩

/-- Depth d represents 2^(d+3) bits. Empty subtrees are skipped. -/
def fastMoments : ℕ → ℕ → ℕ → Moments
  | 0, start, mask => translate start (byteMoments (mask % 256))
  | depth + 1, start, mask =>
    if mask == 0 then ⟨0, 0, 0⟩ else
    let half := 2 ^ (depth + 3)
    merge (fastMoments depth start (mask % 2 ^ half))
      (fastMoments depth (start + half) (mask / 2 ^ half))

def windowMoments (mask shift len : ℕ) : Moments :=
  fastMoments 10 1 (mask / 2 ^ shift % 2 ^ len)

def stepFromMoments (v a : ℕ) (s : Moments) : ℕ :=
  let ell := s.count * a - s.first
  let u := s.count * a ^ 2 - a * s.first + s.second
  let e := ell ^ 2 - s.count * a ^ 2
  v * ((a ^ 3 - u) * (2 * a ^ 4 + e)) / (2 * a ^ 7)

def fastMomentStep (v a mask shift len : ℕ) : ℕ :=
  stepFromMoments v a (windowMoments mask shift len)

end RosserBitMoments

namespace RosserLogCertificate


def scale : ℕ := 2 ^ 64

/-- `p` represents the current odd power, `q` the squared series argument. -/
def seriesRun (D q : ℕ) : ℕ → ℕ → ℕ → ℕ
  | _, _, 0 => 0
  | j, p, terms + 1 => p / (2 * j + 1) +
      seriesRun D q (j + 1) (p * q / D) terms

def atanhLower (num den : ℕ) : ℕ :=
  let z := num * scale / den
  let q := z * z / scale
  2 * seriesRun scale q 0 z 12

/-- One shared constant, checked from the same twelve-term integer algorithm. -/
def logTwoLower : ℕ := 12786308645200714054

def logLower (n : ℕ) : ℕ :=
  let k := Nat.log2 n
  let t := 2 ^ k
  k * logTwoLower + atanhLower (n - t) (n + t)

end RosserLogCertificate

namespace RosserBlockCheck

open RosserLogCertificate

def sqrtUpper (b : ℕ) : ℕ := Nat.sqrt b + 1

def check (a b v : ℕ) : Bool :=
  decide (0 < v ∧
    scale * scale * 10 ^ 8 * sqrtUpper b <
      v * 178107239 * (logLower a * sqrtUpper b + 2 * scale))

end RosserBlockCheck

namespace RosserScan

open RosserBitSieve AlternativeProductMoments RosserLogCertificate RosserBlockCheck RosserBitMoments

/-- Force a natural-number state before the next recursive call. This avoids
re-evaluating a growing expression during kernel reduction. -/
def forceNat {α : Type} (n : ℕ) (f : ℕ → α) : α :=
  match n with
  | 0 => f 0
  | n + 1 => f (n + 1)

def stepOffsets (base mask a b : ℕ) : List ℕ :=
  windowOffsets 13 mask (a - base) (b - a)

def stepCheck (a b v : ℕ) (ds : List ℕ) : Bool :=
  decide (2 ≤ a ∧ a < b ∧ b - a ≤ 2 ^ 13 ∧
    firstMoment ds ≤ ds.length * a ∧ upperNumerator a ds ≤ a ^ 3) &&
      check a b (momentStep v a ds)

def stepData (base mask a b v : ℕ) : Bool × ℕ :=
  let s := windowMoments mask (a - base) (b - a)
  let w := stepFromMoments v a s
  (decide (2 ≤ a ∧ a < b ∧ b - a ≤ 2 ^ 13 ∧
    s.first ≤ s.count * a ∧ s.count * a ^ 2 - a * s.first + s.second ≤ a ^ 3) &&
      check a b w, w)

/-- Try a block, halving its width if the numerical test does not pass. -/
def attempt (base top mask a v : ℕ) : ℕ → ℕ → Option (ℕ × ℕ)
  | 0, _ => none
  | fuel + 1, width =>
    let b := min top (a + width)
    let data := stepData base mask a b v
    if data.1 then some (b, data.2)
    else attempt base top mask a v fuel (width / 2)

def run (base top mask : ℕ) : ℕ → ℕ → ℕ → Option ℕ
  | 0, a, v => if a == top then some v else none
  | fuel + 1, a, v =>
    if a == top then some v else
    match attempt base top mask a v 20 (max 1 (Nat.sqrt a / 2)) with
    | none => none
    | some (b, w) => forceNat b (fun b => forceNat w (fun w => run base top mask fuel b w))

end RosserScan

namespace RosserSieveData

open RosserBitSieve RosserScan

def divisors : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999, 2003, 2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143, 2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647, 2657, 2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731, 2741, 2749, 2753, 2767, 2777, 2789, 2791, 2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861, 2879, 2887, 2897, 2903, 2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971, 2999, 3001, 3011, 3019, 3023, 3037, 3041, 3049, 3061, 3067, 3079, 3083, 3089, 3109, 3119, 3121, 3137, 3163, 3167, 3169, 3181, 3187, 3191, 3203, 3209, 3217, 3221, 3229, 3251, 3253, 3257, 3259, 3271, 3299, 3301, 3307, 3313, 3319, 3323, 3329, 3331, 3343, 3347, 3359, 3361, 3371, 3373, 3389, 3391, 3407, 3413, 3433, 3449, 3457, 3461, 3463, 3467, 3469, 3491, 3499, 3511, 3517, 3527, 3529, 3533, 3539, 3541, 3547, 3557, 3559, 3571, 3581, 3583, 3593, 3607, 3613, 3617, 3623, 3631, 3637, 3643, 3659, 3671, 3673, 3677, 3691, 3697, 3701, 3709, 3719, 3727, 3733, 3739, 3761, 3767, 3769, 3779, 3793, 3797, 3803, 3821, 3823, 3833, 3847, 3851, 3853, 3863, 3877, 3881, 3889, 3907, 3911, 3917, 3919, 3923, 3929, 3931, 3943, 3947, 3967, 3989, 4001, 4003, 4007, 4013, 4019, 4021, 4027, 4049, 4051, 4057, 4073, 4079, 4091, 4093, 4099, 4111, 4127, 4129, 4133, 4139, 4153, 4157, 4159, 4177, 4201, 4211, 4217, 4219, 4229, 4231, 4241, 4243, 4253, 4259, 4261, 4271, 4273, 4283, 4289, 4297, 4327, 4337, 4339, 4349, 4357, 4363, 4373, 4391, 4397, 4409, 4421, 4423, 4441, 4447, 4451, 4457, 4463, 4481, 4483, 4493, 4507, 4513, 4517, 4519, 4523, 4547, 4549, 4561, 4567, 4583, 4591, 4597, 4603, 4621, 4637, 4639, 4643, 4649, 4651, 4657, 4663, 4673, 4679, 4691, 4703, 4721, 4723, 4729, 4733, 4751, 4759, 4783, 4787, 4789, 4793, 4799, 4801, 4813, 4817, 4831, 4861, 4871, 4877, 4889, 4903, 4909, 4919, 4931, 4933, 4937, 4943, 4951, 4957, 4967, 4969, 4973, 4987, 4993, 4999, 5003, 5009, 5011, 5021, 5023, 5039, 5051, 5059, 5077, 5081, 5087, 5099, 5101, 5107, 5113, 5119, 5147, 5153, 5167, 5171, 5179, 5189, 5197, 5209, 5227, 5231, 5233, 5237, 5261, 5273, 5279, 5281, 5297, 5303, 5309, 5323, 5333, 5347, 5351, 5381, 5387, 5393, 5399, 5407, 5413, 5417, 5419, 5431, 5437, 5441, 5443, 5449, 5471, 5477, 5479, 5483, 5501, 5503, 5507, 5519, 5521, 5527, 5531, 5557, 5563, 5569, 5573, 5581, 5591, 5623, 5639, 5641, 5647, 5651, 5653, 5657, 5659, 5669, 5683, 5689, 5693, 5701, 5711, 5717, 5737, 5741, 5743, 5749, 5779, 5783, 5791, 5801, 5807, 5813, 5821, 5827, 5839, 5843, 5849, 5851, 5857, 5861, 5867, 5869, 5879, 5881, 5897, 5903, 5923, 5927, 5939, 5953, 5981, 5987, 6007, 6011, 6029, 6037, 6043, 6047, 6053, 6067, 6073, 6079, 6089, 6091, 6101, 6113, 6121, 6131, 6133, 6143, 6151, 6163, 6173, 6197, 6199, 6203, 6211, 6217, 6221, 6229, 6247, 6257, 6263, 6269, 6271, 6277, 6287, 6299, 6301, 6311, 6317, 6323, 6329, 6337, 6343, 6353, 6359, 6361, 6367, 6373, 6379, 6389, 6397, 6421, 6427, 6449, 6451, 6469, 6473, 6481, 6491, 6521, 6529, 6547, 6551, 6553, 6563, 6569, 6571, 6577, 6581, 6599, 6607, 6619, 6637, 6653, 6659, 6661, 6673, 6679, 6689, 6691, 6701, 6703, 6709, 6719, 6733, 6737, 6761, 6763, 6779, 6781, 6791, 6793, 6803, 6823, 6827, 6829, 6833, 6841, 6857, 6863, 6869, 6871, 6883, 6899, 6907, 6911, 6917, 6947, 6949, 6959, 6961, 6967, 6971, 6977, 6983, 6991, 6997, 7001, 7013, 7019, 7027, 7039, 7043, 7057, 7069, 7079, 7103, 7109, 7121, 7127, 7129, 7151, 7159, 7177, 7187, 7193, 7207, 7211, 7213, 7219, 7229, 7237, 7243, 7247, 7253, 7283, 7297, 7307, 7309, 7321, 7331, 7333, 7349, 7351, 7369, 7393, 7411, 7417, 7433, 7451, 7457, 7459, 7477, 7481, 7487, 7489, 7499, 7507, 7517, 7523, 7529, 7537, 7541, 7547, 7549, 7559, 7561, 7573, 7577, 7583, 7589, 7591, 7603, 7607, 7621, 7639, 7643, 7649, 7669, 7673, 7681, 7687, 7691, 7699, 7703, 7717, 7723, 7727, 7741, 7753, 7757, 7759, 7789, 7793, 7817, 7823, 7829, 7841, 7853, 7867, 7873, 7877, 7879, 7883, 7901, 7907, 7919, 7927, 7933, 7937, 7949, 7951, 7963, 7993, 8009, 8011, 8017, 8039, 8053, 8059, 8069, 8081, 8087, 8089, 8093, 8101, 8111, 8117, 8123, 8147, 8161, 8167, 8171, 8179, 8191, 8209, 8219, 8221, 8231, 8233, 8237, 8243, 8263, 8269, 8273, 8287, 8291, 8293, 8297, 8311, 8317, 8329, 8353, 8363, 8369, 8377, 8387, 8389, 8419, 8423, 8429, 8431, 8443, 8447, 8461, 8467, 8501, 8513, 8521, 8527, 8537, 8539, 8543, 8563, 8573, 8581, 8597, 8599, 8609, 8623, 8627, 8629, 8641, 8647, 8663, 8669, 8677, 8681, 8689, 8693, 8699, 8707, 8713, 8719, 8731, 8737, 8741, 8747, 8753, 8761, 8779, 8783, 8803, 8807, 8819, 8821, 8831, 8837, 8839, 8849, 8861, 8863, 8867, 8887, 8893, 8923, 8929, 8933, 8941, 8951, 8963, 8969, 8971, 8999, 9001, 9007, 9011, 9013, 9029, 9041, 9043, 9049, 9059, 9067, 9091, 9103, 9109, 9127, 9133, 9137, 9151, 9157, 9161, 9173, 9181, 9187, 9199, 9203, 9209, 9221, 9227, 9239, 9241, 9257, 9277, 9281, 9283, 9293, 9311, 9319, 9323, 9337, 9341, 9343, 9349, 9371, 9377, 9391, 9397, 9403, 9413, 9419, 9421, 9431, 9433, 9437, 9439, 9461, 9463, 9467, 9473, 9479, 9491, 9497, 9511, 9521, 9533, 9539, 9547, 9551, 9587, 9601, 9613, 9619, 9623, 9629, 9631, 9643, 9649, 9661, 9677, 9679, 9689, 9697, 9719, 9721, 9733, 9739, 9743, 9749, 9767, 9769, 9781, 9787, 9791, 9803, 9811, 9817, 9829, 9833, 9839, 9851, 9857, 9859, 9871, 9883, 9887, 9901, 9907, 9923, 9929, 9931, 9941, 9949, 9967, 9973]

def smallDivisors (base : ℕ) := divisors.filter (fun d => decide (d ≤ base))

def mask (base top : ℕ) := candidateMask (smallDivisors base) (base + 1) (top - base)

def segment (base top v : ℕ) :=
  forceNat (mask base top) (fun m => run base top m 4096 base v)

end RosserSieveData

-- Source: Solutions/RosserProductBlocks.lean
/-!
Reusable, kernel-checked parts of a block certificate for Rosser--Schoenfeld.
This module does not assert the target on [4500, 10^8]. In particular, it does
not trust the Python sieve or import any open platform theorem.
-/

namespace RosserProductCertificate

noncomputable def eulerProduct (n : ℕ) : ℝ :=
  ∏ p ∈ Nat.primesLE n, (p : ℝ) / ((p : ℝ) - 1)

theorem eulerProduct_mono : Monotone eulerProduct := by
  intro a b hab
  apply Finset.prod_le_prod_of_subset_of_one_le (Nat.primesLE_mono hab)
  · intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
    exact div_nonneg (by positivity) (by linarith)
  · intro p hp _
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
    apply (le_div_iff₀ (by linarith : (0 : ℝ) < p - 1)).mpr
    linarith

/-- A single comparison closes every real x in [a, B]. The square-root
term is bounded at B, while the logarithm is bounded at a. -/
theorem block_bound (B : ℕ) (a x U g L S : ℝ)
    (ha : 1 ≤ a) (hax : a ≤ x) (hxB : x ≤ B)
    (hU : eulerProduct B ≤ U)
    (hg : g ≤ Real.exp Real.eulerMascheroniConstant)
    (hL0 : 0 ≤ L) (hL : L ≤ Real.log a)
    (hS : 0 < S) (hBS : (B : ℝ) ≤ S ^ 2)
    (hcheck : U < g * (L + 2 / S)) :
    eulerProduct ⌊x⌋₊ <
      Real.exp Real.eulerMascheroniConstant * Real.log x +
        2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x := by
  have hxpos : 0 < x := by linarith
  have hlog : L ≤ Real.log x := hL.trans (Real.log_le_log (by linarith) hax)
  have hsqrt : Real.sqrt x ≤ S :=
    Real.sqrt_le_iff.mpr ⟨hS.le, hxB.trans hBS⟩
  have hdiv : (2 : ℝ) / S ≤ 2 / Real.sqrt x :=
    div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.mpr hxpos) hsqrt
  have hbase : 0 ≤ L + 2 / S := by positivity
  calc
    eulerProduct ⌊x⌋₊ ≤ eulerProduct B := eulerProduct_mono (Nat.floor_le_of_le hxB)
    _ ≤ U := hU
    _ < g * (L + 2 / S) := hcheck
    _ ≤ Real.exp Real.eulerMascheroniConstant * (L + 2 / S) :=
      mul_le_mul_of_nonneg_right hg hbase
    _ ≤ Real.exp Real.eulerMascheroniConstant * (Real.log x + 2 / Real.sqrt x) :=
      mul_le_mul_of_nonneg_left (add_le_add hlog hdiv) (Real.exp_pos _).le
    _ = _ := by ring

/-- Integer update for a downward-rounded reciprocal product. -/
def downStep (v p : ℕ) : ℕ := v * (p - 1) / p

/-- Rounding down preserves a lower bound for the reciprocal product. -/
theorem downStep_sound (D v p : ℕ) (Q : ℝ)
    (hD : 0 < D) (hp : 2 ≤ p) (hv : (v : ℝ) / D ≤ Q) :
    (downStep v p : ℝ) / D ≤ Q * (((p : ℝ) - 1) / p) := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hround : (downStep v p : ℝ) ≤ (v : ℝ) * (p - 1) / p := by
    simpa [downStep, Nat.cast_mul, hcast] using
      (Nat.cast_div_le (m := v * (p - 1)) (n := p) (α := ℝ))
  calc
    (downStep v p : ℝ) / D ≤ ((v : ℝ) * (p - 1) / p) / D :=
      div_le_div_of_nonneg_right hround hD'.le
    _ = ((v : ℝ) / D) * ((p - 1) / p) := by ring
    _ ≤ Q * ((p - 1) / p) :=
      mul_le_mul_of_nonneg_right hv (div_nonneg (by linarith) (by linarith))

/-- The rounding invariant for an entire list, including repeated or composite
entries. A separate coverage proof connects this list to the target primes. -/
theorem downRun_sound (ps : List ℕ) (D v : ℕ) (Q : ℝ)
    (hD : 0 < D) (hps : ∀ p ∈ ps, 2 ≤ p) (hv : (v : ℝ) / D ≤ Q) :
    ((ps.foldl downStep v : ℕ) : ℝ) / D ≤
      Q * (ps.map (fun (p : ℕ) => ((p : ℝ) - 1) / p)).prod := by
  induction ps generalizing v Q with
  | nil => simpa using hv
  | cons p ps ih =>
    have hp : 2 ≤ p := hps p (by simp)
    have htail : ∀ q ∈ ps, 2 ≤ q := by
      intro q hq
      exact hps q (by simp [hq])
    have hstep := downStep_sound D v p Q hD hp hv
    simpa [List.foldl_cons, List.map_cons, List.prod_cons, mul_assoc] using
      ih (downStep v p) (Q * (((p : ℝ) - 1) / p)) htail hstep

/-- Convert a positive lower bound on the reciprocal product into the needed
upper bound on the original Euler product. -/
theorem eulerProduct_le_of_reciprocal (n : ℕ) (r : ℝ) (hr : 0 < r)
    (hrecip : r ≤ ∏ p ∈ Nat.primesLE n, (((p : ℝ) - 1) / p)) :
    eulerProduct n ≤ 1 / r := by
  have hnonneg : 0 ≤ eulerProduct n := by
    apply Finset.prod_nonneg
    intro p hp
    have h : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
    exact div_nonneg (by positivity) (by linarith)
  have hcancel :
      (∏ p ∈ Nat.primesLE n, (((p : ℝ) - 1) / p)) * eulerProduct n = 1 := by
    unfold eulerProduct
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro p hp
    have h : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
    field_simp [show (p : ℝ) - 1 ≠ 0 by linarith]
  apply (le_div_iff₀ hr).mpr
  have := mul_le_mul_of_nonneg_right hrecip hnonneg
  nlinarith

/-- Sieving with any divisor d >= 2 cannot discard a prime p > d.
This is the mathematical invariant required of an optimized sieve. -/
theorem prime_survives_sieve (p d : ℕ) (hp : Nat.Prime p) (hd : 2 ≤ d)
    (hdp : d < p) : ¬d ∣ p := by
  intro hdiv
  rcases hp.eq_one_or_self_of_dvd d hdiv with h | h <;> omega

/-- No assertion of primality is needed for retained sieve candidates:
including extra integers >= 2 only makes a reciprocal-product bound smaller. -/
theorem reciprocal_product_of_superset (s t : Finset ℕ)
    (hst : s ⊆ t) (ht : ∀ p ∈ t, 2 ≤ p) :
    (∏ p ∈ t, (((p : ℝ) - 1) / p)) ≤ ∏ p ∈ s, (((p : ℝ) - 1) / p) := by
  apply Finset.prod_le_prod_of_subset_of_le_one hst
  · intro p hp
    have h : (2 : ℝ) ≤ p := by exact_mod_cast ht p hp
    exact div_nonneg (by linarith) (by linarith)
  · intro p hp _
    have h : (2 : ℝ) ≤ p := by exact_mod_cast ht p hp
    apply (div_le_one (by linarith : (0 : ℝ) < p)).mpr
    linarith

/-- The short positive series used by the experiment for logarithm bounds.
Range reduction n = 2^k * m keeps its argument at most 1/3. -/
theorem log_series_lower (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z < 1) (terms : ℕ) :
    2 * (∑ i ∈ Finset.range terms, z ^ (2 * i + 1) / (2 * i + 1)) ≤
      Real.log ((1 + z) / (1 - z)) := by
  have h := Real.sum_range_le_log_div hz0 hz1 terms
  linarith

end RosserProductCertificate

-- Source: Solutions/ImportedGammaLower.lean
/-!
Accepted Prove2Me proof by andreaskapfer, submission
https://prove2.me/submissions/5b7f3df2-2c10-4572-822a-c64a9d656697
for theorem 9563c569-6ee9-44dd-84a3-163bdd7ea018.
Only changes: added provenance and an enclosing namespace; removed #print;
replaced the all-tactics import with the specific imports used by the proof.
The complete proof is included so local builds do not trust a platform status.
-/

namespace Prove2MeGammaLower

set_option maxRecDepth 1000000

open Real Filter

set_option maxHeartbeats 2000000

namespace TaoFivePrimes


lemma pw (k : ℕ) (hk : 201 ≤ k) :
    2/(2*(k:ℝ)+1) + (2/3)/((2*(k:ℝ)+1)*((2*(k:ℝ)+1)^2 - 1)) - 1/((k:ℝ)+1)
      ≤ 18/((6*(k:ℝ)+1)*(6*(k:ℝ)+7)) := by
  have hk403 : (403:ℝ) ≤ 2*(k:ℝ)+1 := by exact_mod_cast (by omega : 403 ≤ 2*k+1)
  have h2 : (0:ℝ) < 2*(k:ℝ)+1 := by linarith
  have hsq : (0:ℝ) < (2*(k:ℝ)+1)^2 - 1 := by nlinarith [sq_nonneg ((2*(k:ℝ)+1) - 403), hk403]
  have hk1 : (0:ℝ) < (k:ℝ)+1 := by positivity
  have hk0 : (0:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
  have h6 : (0:ℝ) < 6*(k:ℝ)+1 := by linarith
  have h7 : (0:ℝ) < 6*(k:ℝ)+7 := by linarith
  have hu : (0:ℝ) ≤ (k:ℝ) - 201 := by linarith
  have hA : 2/(2*(k:ℝ)+1) + (2/3)/((2*(k:ℝ)+1)*((2*(k:ℝ)+1)^2 - 1))
      = (6*((2*(k:ℝ)+1)^2 - 1) + 2)/(3*(2*(k:ℝ)+1)*((2*(k:ℝ)+1)^2 - 1)) := by
    field_simp <;> ring_nf
  have hB : 18/((6*(k:ℝ)+1)*(6*(k:ℝ)+7)) + 1/((k:ℝ)+1)
      = (18*((k:ℝ)+1) + (6*(k:ℝ)+1)*(6*(k:ℝ)+7))/((6*(k:ℝ)+1)*(6*(k:ℝ)+7)*((k:ℝ)+1)) := by
    field_simp <;> ring_nf
  suffices hs : (6*((2*(k:ℝ)+1)^2 - 1) + 2)/(3*(2*(k:ℝ)+1)*((2*(k:ℝ)+1)^2 - 1))
      ≤ (18*((k:ℝ)+1) + (6*(k:ℝ)+1)*(6*(k:ℝ)+7))/((6*(k:ℝ)+1)*(6*(k:ℝ)+7)*((k:ℝ)+1)) by
    linarith [hA, hB]
  rw [div_le_iff₀ (by positivity : (0:ℝ) < 3*(2*(k:ℝ)+1)*((2*(k:ℝ)+1)^2 - 1))]
  rw [div_mul_eq_mul_div]
  rw [le_div_iff₀ (by positivity : (0:ℝ) < ((6*(k:ℝ)+1)*(6*(k:ℝ)+7))*((k:ℝ)+1))]
  have hdec : (0:ℝ) ≤ 36*((k:ℝ)-201)^2 + 14494*((k:ℝ)-201) + 1458844 := by positivity
  nlinarith [hdec, hu, sq_nonneg ((k:ℝ)-201)]



lemma log_series_le (k : ℕ) (hk : 1 ≤ k) :
    Real.log (1 + 1/(k:ℝ)) ≤
      2/(2*(k:ℝ)+1) + (2/3)/((2*(k:ℝ)+1)*((2*(k:ℝ)+1)^2 - 1)) := by
  have hk0 : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  have ha : (0:ℝ) ≤ 1/(k:ℝ) := by positivity
  have hHS : HasSum (fun j : ℕ => 2 * (1 / (2 * (j:ℝ) + 1)) * ((1/(k:ℝ)) / ((1/(k:ℝ)) + 2)) ^ (2 * j + 1))
      (Real.log (1 + 1/(k:ℝ))) := Real.hasSum_log_one_add ha
  have hq : (1/(k:ℝ)) / ((1/(k:ℝ)) + 2) = 1/(2*(k:ℝ)+1) := by
    field_simp
    ring
  simp only [hq] at hHS
  have hsumm : Summable (fun j : ℕ => 2 * (1 / (2 * (j:ℝ) + 1)) * (1/(2*(k:ℝ)+1)) ^ (2 * j + 1)) :=
    hHS.summable
  have hsplit := Summable.sum_add_tsum_nat_add 1 hsumm
  rw [Finset.sum_range_one, hHS.tsum_eq] at hsplit
  have htail_le : (∑' i : ℕ, (fun j : ℕ => 2 * (1 / (2 * (j:ℝ) + 1)) * (1/(2*(k:ℝ)+1)) ^ (2 * j + 1)) (i+1))
      ≤ (2/3) * (1/(2*(k:ℝ)+1))^3 / (1 - (1/(2*(k:ℝ)+1))^2) := by
    have hq0 : (0:ℝ) ≤ (1/(2*(k:ℝ)+1))^2 := sq_nonneg _
    have hq1 : (1/(2*(k:ℝ)+1))^2 < 1 := by
      rw [div_pow, one_pow, div_lt_one (by positivity)]
      nlinarith [hk0, sq_nonneg ((k:ℝ))]
    have hgeo : HasSum (fun j : ℕ => (2/3) * (1/(2*(k:ℝ)+1))^3 * ((1/(2*(k:ℝ)+1))^2)^j)
        ((2/3) * (1/(2*(k:ℝ)+1))^3 / (1 - (1/(2*(k:ℝ)+1))^2)) := by
      have := (hasSum_geometric_of_norm_lt_one
        (show ‖(1/(2*(k:ℝ)+1))^2‖ < 1 by rwa [Real.norm_eq_abs, abs_of_nonneg hq0])).mul_left
        ((2/3) * (1/(2*(k:ℝ)+1))^3)
      rwa [div_eq_mul_inv]
    have hmain := ((summable_nat_add_iff 1).mpr hsumm).tsum_le_tsum (fun j => by
      push_cast
      have hcoe : 2 * (1 / (2 * ((j:ℝ) + 1) + 1)) ≤ 2/3 := by
        rw [show 2 * (1 / (2 * ((j:ℝ) + 1) + 1)) = 2/(2*((j:ℝ)+1)+1) by ring]
        rw [div_le_iff₀ (by positivity : (0:ℝ) < 2*((j:ℝ)+1)+1)]
        linarith
      have hpow : (1/(2*(k:ℝ)+1)) ^ (2 * (j + 1) + 1)
          = (1/(2*(k:ℝ)+1))^3 * ((1/(2*(k:ℝ)+1))^2)^j := by
        rw [show 2 * (j + 1) + 1 = 3 + 2 * j by omega, pow_add, pow_mul]
      calc 2 * (1 / (2 * ((j:ℝ) + 1) + 1)) * (1/(2*(k:ℝ)+1)) ^ (2 * (j + 1) + 1)
          = (2 * (1 / (2 * ((j:ℝ) + 1) + 1))) * ((1/(2*(k:ℝ)+1))^3 * ((1/(2*(k:ℝ)+1))^2)^j) := by
            rw [hpow]
        _ ≤ (2/3) * ((1/(2*(k:ℝ)+1))^3 * ((1/(2*(k:ℝ)+1))^2)^j) := by
            apply mul_le_mul_of_nonneg_right hcoe
            positivity
        _ = (2/3) * (1/(2*(k:ℝ)+1))^3 * ((1/(2*(k:ℝ)+1))^2)^j := by ring) hgeo.summable
    exact hmain.trans_eq hgeo.tsum_eq
  have hconv : (2/3) * (1/(2*(k:ℝ)+1))^3 / (1 - (1/(2*(k:ℝ)+1))^2)
      = (2/3)/((2*(k:ℝ)+1)*((2*(k:ℝ)+1)^2 - 1)) := by
    field_simp
  have hlog : Real.log (1 + 1/(k:ℝ)) = 2 * (1/(2*(k:ℝ)+1))
      + (∑' i : ℕ, (fun j : ℕ => 2 * (1 / (2 * (j:ℝ) + 1)) * (1/(2*(k:ℝ)+1)) ^ (2 * j + 1)) (i+1)) := by
    rw [← hsplit]
    congr 1
    norm_num
  have hid : 2 * (1/(2*(k:ℝ)+1)) = 2/(2*(k:ℝ)+1) := by ring
  have htail_le' : (∑' i : ℕ, (fun j : ℕ => 2 * (1 / (2 * (j:ℝ) + 1)) * (1/(2*(k:ℝ)+1)) ^ (2 * j + 1)) (i+1))
      ≤ (2/3)/((2*(k:ℝ)+1)*((2*(k:ℝ)+1)^2 - 1)) := htail_le.trans_eq hconv
  rw [hlog]
  linarith [htail_le', hid]


lemma term_le (k : ℕ) (hk : 201 ≤ k) :
    ZetaAsymptotics.term k 1 ≤ 18/((6*(k:ℝ)+1)*(6*(k:ℝ)+7)) := by
  have hk0 : (0:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
  rw [ZetaAsymptotics.term_one (by omega : 0 < k)]
  have h1 : Real.log ((k:ℝ)+1) - Real.log (k:ℝ) = Real.log (1 + 1/(k:ℝ)) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 1
    field_simp
  rw [h1]
  linarith [log_series_le k (by omega : 1 ≤ k), pw k hk]

lemma tail_bound : (∑' k : ℕ, ZetaAsymptotics.term (k + 201) 1) ≤ 3/1207 := by
  have htel : ∀ k : ℕ, (18:ℝ)/((6*(((k+201:ℕ)):ℝ)+1)*(6*(((k+201:ℕ)):ℝ)+7))
      = (1/2)/((k:ℝ)+201+1/6) - (1/2)/(((k+1:ℕ):ℝ)+201+1/6) := by
    intro k
    push_cast
    have h1 : (6*((k:ℝ)+201)+1) ≠ 0 := by positivity
    have h2 : (6*((k:ℝ)+201)+7) ≠ 0 := by positivity
    have h3 : ((k:ℝ)+201+1/6) ≠ 0 := by positivity
    have h4 : ((k:ℝ)+1+201+1/6) ≠ 0 := by positivity
    field_simp [h1, h2, h3, h4]
    ring
  have hu_tend : Tendsto (fun n : ℕ => (1/2)/((n:ℝ)+201+1/6)) atTop (nhds 0) := by
    have h1 : Tendsto (fun n : ℕ => ((n:ℝ) + (201 + 1/6))) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun n : ℕ => (((n:ℝ) + (201 + 1/6)))⁻¹) atTop (nhds 0) := h1.inv_tendsto_atTop
    have h3 : Tendsto (fun n : ℕ => (1/2) * (((n:ℝ) + (201 + 1/6)))⁻¹) atTop (nhds (1/2 * 0)) :=
      tendsto_const_nhds.mul h2
    rw [mul_zero] at h3
    simpa [div_eq_mul_inv, add_assoc] using h3
  have hRsum : HasSum (fun k : ℕ => (18:ℝ)/((6*(((k+201:ℕ)):ℝ)+1)*(6*(((k+201:ℕ)):ℝ)+7)))
      ((1/2)/((201:ℝ)+1/6)) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg (fun k => by positivity)]
    have hps : ∀ n, ∑ k ∈ Finset.range n, (18:ℝ)/((6*(((k+201:ℕ)):ℝ)+1)*(6*(((k+201:ℕ)):ℝ)+7))
        = (1/2)/((0:ℝ)+201+1/6) - (1/2)/((n:ℝ)+201+1/6) := by
      intro n
      calc ∑ k ∈ Finset.range n, (18:ℝ)/((6*(((k+201:ℕ)):ℝ)+1)*(6*(((k+201:ℕ)):ℝ)+7))
          = ∑ k ∈ Finset.range n, ((1/2)/((k:ℝ)+201+1/6) - (1/2)/(((k+1:ℕ):ℝ)+201+1/6)) := by
            apply Finset.sum_congr rfl
            intro k _
            exact htel k
        _ = -(∑ k ∈ Finset.range n, ((1/2)/(((k+1:ℕ):ℝ)+201+1/6) - (1/2)/((k:ℝ)+201+1/6))) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro k _
            ring
        _ = -((1/2)/((n:ℝ)+201+1/6) - (1/2)/(((0:ℕ):ℝ)+201+1/6)) := by
            rw [Finset.sum_range_sub (fun k : ℕ => (1/2)/((k:ℝ)+201+1/6)) n]
        _ = (1/2)/((0:ℝ)+201+1/6) - (1/2)/((n:ℝ)+201+1/6) := by
            simp only [Nat.cast_zero]
            ring
    simp_rw [hps]
    simpa using tendsto_const_nhds.sub hu_tend
  have hsumg : Summable (fun k : ℕ => ZetaAsymptotics.term (k + 201) 1) := by
    have hf : Summable (fun n : ℕ => ZetaAsymptotics.term (n+1) 1) :=
      ZetaAsymptotics.term_tsum_one.summable
    exact (summable_nat_add_iff 200).mpr hf
  have hRsummable : Summable (fun k : ℕ =>
      (18:ℝ)/((6*(((k+201:ℕ)):ℝ)+1)*(6*(((k+201:ℕ)):ℝ)+7))) := hRsum.summable
  have key := hsumg.tsum_le_tsum (fun k => term_le (k+201) (by omega)) hRsummable
  rw [hRsum.tsum_eq] at key
  norm_num at key ⊢
  exact key

/-- Lower bound for Euler--Mascheroni: `57721565/10^8 ≤ γ`. -/
theorem solution : (57721565/10^8 : ℝ) ≤ Real.eulerMascheroniConstant := by
  have hf : Summable (fun n : ℕ => ZetaAsymptotics.term (n+1) 1) :=
    ZetaAsymptotics.term_tsum_one.summable
  have hsplit := Summable.sum_add_tsum_nat_add 200 hf
  rw [ZetaAsymptotics.term_tsum_one.tsum_eq] at hsplit
  have htail_eq : (∑' i : ℕ, (fun n : ℕ => ZetaAsymptotics.term (n+1) 1) (i+200))
      = (∑' k : ℕ, ZetaAsymptotics.term (k+201) 1) := by
    apply tsum_congr
    intro i
    congr 1
  rw [htail_eq] at hsplit
  have htermSum : (∑ i ∈ Finset.range 200, ZetaAsymptotics.term (i+1) 1)
      = Real.log 201 - (harmonic 201 : ℝ) + 1 := by
    have h := ZetaAsymptotics.termSum_one 200
    unfold ZetaAsymptotics.termSum at h
    rw [show ((200:ℕ):ℝ) + 1 = 201 by norm_num, show (200 + 1 : ℕ) = 201 by norm_num] at h
    exact h
  rw [htermSum] at hsplit
  have hγ : Real.eulerMascheroniConstant = (harmonic 201 : ℝ) - Real.log 201
      - (∑' k : ℕ, ZetaAsymptotics.term (k+201) 1) := by
    linarith
  have hr : Real.log 201 ≤ (530330491/10^8 : ℝ) := by
    rw [Real.log_le_iff_le_exp (by norm_num : (0:ℝ) < 201)]
    calc (201:ℝ) ≤ (2.7182818283:ℝ)^5 * (∑ i ∈ Finset.range 10, (30330491/10^8:ℝ)^i / (i.factorial : ℝ)) := by
          norm_num
      _ ≤ (Real.exp 1)^5 * Real.exp (30330491/10^8) := by
          gcongr
          · exact le_of_lt Real.exp_one_gt_d9
          · exact Real.sum_le_exp_of_nonneg (by norm_num) 10
      _ = Real.exp 5 * Real.exp (30330491/10^8) := by
          rw [← Real.exp_nat_mul 1 5]
          norm_num
      _ = Real.exp (5 + 30330491/10^8) := by rw [← Real.exp_add]
      _ = Real.exp (530330491/10^8) := by norm_num
  have hnum : (57721565/10^8 : ℝ) ≤ (harmonic 201 : ℝ) - (530330491/10^8) - 3/1207 := by
    norm_num [harmonic]
  calc (57721565/10^8 : ℝ) ≤ (harmonic 201 : ℝ) - (530330491/10^8) - 3/1207 := hnum
    _ ≤ Real.eulerMascheroniConstant := by
        rw [hγ]
        linarith [hr, tail_bound]

end TaoFivePrimes

open TaoFivePrimes

/-- The verification harness looks for `theorem solution` in the root
namespace, so the namespaced proof above is re-exported at the root. -/
theorem solution : (57721565/10^8 : ℝ) ≤ Real.eulerMascheroniConstant :=
  TaoFivePrimes.solution


end Prove2MeGammaLower

-- Source: Solutions/RosserProductPilot.lean
/-!
A fully proved pilot interval, using the same downward-rounding scheme as
scripts/rosser_product_experiment.py. All concrete computations below are
checked by Lean; there is no native_decide or external numerical oracle.
The slow reference prime enumeration is only intended for this small pilot.
-/

namespace RosserProductCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def referencePrimes (B : ℕ) : List ℕ :=
  (List.range (B + 1)).filter (fun p => decide (2 ≤ p ∧ Nat.minFac p = p))

theorem referencePrimes_toFinset (B : ℕ) :
    (referencePrimes B).toFinset = Nat.primesLE B := by
  ext p
  simp [referencePrimes, Nat.mem_primesLE, Nat.prime_def_minFac]

theorem referencePrimes_nodup (B : ℕ) : (referencePrimes B).Nodup :=
  List.nodup_range.filter _

theorem referencePrimes_ge_two (B p : ℕ) (hp : p ∈ referencePrimes B) : 2 ≤ p := by
  have h := (List.mem_filter.mp hp).2
  exact (of_decide_eq_true h).1

theorem exp_gamma_lower :
    (178107239 / 10 ^ 8 : ℝ) ≤ Real.exp Real.eulerMascheroniConstant := by
  have h := Real.sum_le_exp_of_nonneg
    (show (0 : ℝ) ≤ 57721565 / 10 ^ 8 by norm_num) 16
  have hnum : (178107239 / 10 ^ 8 : ℝ) ≤
      ∑ i ∈ Finset.range 16, (57721565 / 10 ^ 8 : ℝ) ^ i / i.factorial := by
    norm_num [Finset.sum_range_succ]
  exact (hnum.trans h).trans (Real.exp_le_exp.mpr Prove2MeGammaLower.solution)

theorem log_4500_lower : (8411832675757 / 10 ^ 12 : ℝ) ≤ Real.log 4500 := by
  have htwo := log_series_lower (1 / 3 : ℝ) (by norm_num) (by norm_num) 12
  have hrest := log_series_lower (101 / 2149 : ℝ) (by norm_num) (by norm_num) 12
  norm_num [Finset.sum_range_succ] at htwo hrest
  have heq : Real.log 4500 = 12 * Real.log 2 + Real.log (1125 / 1024) := by
    have hn : (4500 : ℝ) = 2 ^ 12 * (1125 / 1024) := by norm_num
    rw [hn, Real.log_mul (by positivity) (by positivity), Real.log_pow]
    norm_num
  rw [heq]
  linarith

/-- A kernel computation with a fixed 64-bit denominator; no huge exact
numerator and denominator for the Euler product are constructed. -/
theorem reciprocal_4533_lower :
    (1227903923884082104 : ℝ) / 2 ^ 64 ≤
      ∏ p ∈ Nat.primesLE 4533, (((p : ℝ) - 1) / p) := by
  have hcalc : (referencePrimes 4533).foldl downStep (2 ^ 64) =
      1227903923884082104 := by decide +kernel
  have h := downRun_sound (referencePrimes 4533) (2 ^ 64) (2 ^ 64) 1
    (by norm_num) (referencePrimes_ge_two 4533) (by norm_num)
  rw [hcalc] at h
  rw [← List.prod_toFinset _ (referencePrimes_nodup 4533), referencePrimes_toFinset] at h
  simpa only [Nat.cast_pow, Nat.cast_ofNat, one_mul] using h

/-- The original platform inequality, proved without additional hypotheses
on the closed real interval [4500, 4533]. -/
theorem product_bound_4500_to_4533 (x : ℝ) (hx : 4500 ≤ x) (hx' : x ≤ 4533) :
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) <
      Real.exp Real.eulerMascheroniConstant * Real.log x +
        2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x := by
  have hu := eulerProduct_le_of_reciprocal 4533
    (1227903923884082104 / 2 ^ 64) (by norm_num) reciprocal_4533_lower
  apply block_bound 4533 4500 x (1 / (1227903923884082104 / 2 ^ 64))
    (178107239 / 10 ^ 8) (8411832675757 / 10 ^ 12) 68
    (by norm_num) hx hx' hu exp_gamma_lower (by norm_num) log_4500_lower
    (by norm_num) (by norm_num)
  norm_num

end RosserProductCertificate

-- Source: Solutions/RosserLogCertificate.lean
/-!
A table-free lower bound for log(n). All evaluation uses natural numbers
with fixed denominator 2^64. There are twelve positive atanh-series terms;
every division, including the power recurrence, rounds downward.
-/

namespace RosserLogCertificate

theorem scale_pos : 0 < scale := by decide

theorem rounded_mul_lower (D p q : ℕ) (x y : ℝ) (hD : 0 < D)
    (hx0 : 0 ≤ x) (hp : (p : ℝ) / D ≤ x) (hq : (q : ℝ) / D ≤ y) :
    ((p * q / D : ℕ) : ℝ) / D ≤ x * y := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have hround := Nat.cast_div_le (m := p * q) (n := D) (α := ℝ)
  simp only [Nat.cast_mul] at hround
  calc
    ((p * q / D : ℕ) : ℝ) / D ≤ ((p : ℝ) * q / D) / D :=
      div_le_div_of_nonneg_right hround hD0.le
    _ = ((p : ℝ) / D) * ((q : ℝ) / D) := by ring
    _ ≤ x * y := mul_le_mul hp hq (by positivity) hx0

theorem seriesRun_sound (D q : ℕ) (z : ℝ) (hD : 0 < D) (hz : 0 ≤ z)
    (hq : (q : ℝ) / D ≤ z ^ 2) (j p terms : ℕ)
    (hp : (p : ℝ) / D ≤ z ^ (2 * j + 1)) :
    (seriesRun D q j p terms : ℝ) / D ≤
      ∑ i ∈ Finset.range terms,
        z ^ (2 * (j + i) + 1) / (2 * ((j + i : ℕ) : ℝ) + 1) := by
  induction terms generalizing j p with
  | zero => simp [seriesRun]
  | succ terms ih =>
    have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
    have hden : (0 : ℝ) < 2 * j + 1 := by positivity
    have hterm : ((p / (2 * j + 1) : ℕ) : ℝ) / D ≤
        z ^ (2 * j + 1) / (2 * (j : ℝ) + 1) := by
      have hr := Nat.cast_div_le (m := p) (n := 2 * j + 1) (α := ℝ)
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at hr
      calc
        ((p / (2 * j + 1) : ℕ) : ℝ) / D ≤
            ((p : ℝ) / (2 * (j : ℝ) + 1)) / D :=
          div_le_div_of_nonneg_right hr hD0.le
        _ = ((p : ℝ) / D) / (2 * (j : ℝ) + 1) := by ring
        _ ≤ _ := div_le_div_of_nonneg_right hp hden.le
    have hnext : ((p * q / D : ℕ) : ℝ) / D ≤ z ^ (2 * (j + 1) + 1) := by
      have hr := rounded_mul_lower D p q (z ^ (2 * j + 1)) (z ^ 2)
        hD (by positivity) hp hq
      have he : z ^ (2 * j + 1) * z ^ 2 = z ^ (2 * (j + 1) + 1) := by
        rw [← pow_add]
        congr 1
      exact he ▸ hr
    have hi := ih (j + 1) (p * q / D) hnext
    rw [Finset.sum_range_succ']
    simp only [seriesRun, Nat.cast_add, add_div]
    have hshift :
        (∑ i ∈ Finset.range terms,
          z ^ (2 * (j + 1 + i) + 1) / (2 * ((j + 1 + i : ℕ) : ℝ) + 1)) =
        ∑ i ∈ Finset.range terms,
          z ^ (2 * (j + (i + 1)) + 1) / (2 * ((j + (i + 1) : ℕ) : ℝ) + 1) := by
      apply Finset.sum_congr rfl
      intro i _
      have he : j + 1 + i = j + (i + 1) := by omega
      rw [he]
    rw [hshift] at hi
    simpa only [Nat.add_zero, Nat.cast_add, Nat.cast_zero, Nat.cast_one,
      add_zero, add_comm] using add_le_add hi hterm

theorem atanhLower_sound (num den : ℕ) (hden : 0 < den) (hnum : num < den) :
    (atanhLower num den : ℝ) / scale ≤
      Real.log ((1 + (num : ℝ) / den) / (1 - (num : ℝ) / den)) := by
  let z : ℝ := (num : ℝ) / den
  let v := num * scale / den
  let q := v * v / scale
  have hD0 : (0 : ℝ) < scale := by exact_mod_cast scale_pos
  have hden0 : (0 : ℝ) < den := by exact_mod_cast hden
  have hz0 : 0 ≤ z := by dsimp [z]; positivity
  have hz1 : z < 1 := by
    apply (div_lt_one hden0).mpr
    exact_mod_cast hnum
  have hv : (v : ℝ) / scale ≤ z := by
    have hr := Nat.cast_div_le (m := num * scale) (n := den) (α := ℝ)
    simp only [Nat.cast_mul] at hr
    calc
      (v : ℝ) / scale ≤ ((num : ℝ) * scale / den) / scale :=
        div_le_div_of_nonneg_right hr hD0.le
      _ = z := by dsimp [z]; field_simp
  have hq : (q : ℝ) / scale ≤ z ^ 2 := by
    simpa only [pow_two] using rounded_mul_lower scale v v z z scale_pos hz0 hv hv
  have hr := seriesRun_sound scale q z scale_pos hz0 hq 0 v 12
    (by simpa using hv)
  simp only [Nat.zero_add] at hr
  have hl := Real.sum_range_le_log_div hz0 hz1 12
  change (2 * seriesRun scale q 0 v 12 : ℕ) / (scale : ℝ) ≤ _
  push_cast
  change 2 * (seriesRun scale q 0 v 12 : ℝ) / scale ≤
    Real.log ((1 + z) / (1 - z))
  calc
    2 * (seriesRun scale q 0 v 12 : ℝ) / scale =
        2 * ((seriesRun scale q 0 v 12 : ℝ) / scale) := by ring
    _ ≤ _ := by linarith only [hr, hl]

theorem logTwoLower_eval : atanhLower 1 3 = logTwoLower := by decide +kernel

theorem logTwoLower_sound : (logTwoLower : ℝ) / scale ≤ Real.log 2 := by
  have h := atanhLower_sound 1 3 (by decide) (by decide)
  rw [logTwoLower_eval] at h
  norm_num at h ⊢
  exact h

theorem logLower_sound (n : ℕ) (hn : 1 ≤ n) :
    (logLower n : ℝ) / scale ≤ Real.log n := by
  let k := Nat.log2 n
  let t : ℕ := 2 ^ k
  have hn0 : n ≠ 0 := by omega
  have ht0 : 0 < t := by dsimp [t]; positivity
  have htn : t ≤ n := (Nat.le_log2 hn0).mp (le_refl _)
  have hnum : n - t < n + t := by omega
  have hden : 0 < n + t := by omega
  have hrest := atanhLower_sound (n - t) (n + t) hden hnum
  have ht0' : (0 : ℝ) < t := by exact_mod_cast ht0
  have hn0' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hid : (1 + ((n - t : ℕ) : ℝ) / (n + t : ℕ)) /
      (1 - ((n - t : ℕ) : ℝ) / (n + t : ℕ)) = (n : ℝ) / t := by
    rw [Nat.cast_sub htn, Nat.cast_add]
    field_simp [ne_of_gt ht0', ne_of_gt (add_pos hn0' ht0')]
    ring
  rw [hid, Real.log_div (ne_of_gt hn0') (ne_of_gt ht0')] at hrest
  have htlog : Real.log (t : ℝ) = (k : ℝ) * Real.log 2 := by
    simp only [t, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  rw [htlog] at hrest
  have htwo := mul_le_mul_of_nonneg_left logTwoLower_sound
    (show (0 : ℝ) ≤ k by positivity)
  change ((k * logTwoLower + atanhLower (n - t) (n + t) : ℕ) : ℝ) / scale ≤ _
  rw [Nat.cast_add, Nat.cast_mul, add_div, mul_div_assoc]
  linarith only [htwo, hrest]

theorem logLower_4500_eval : logLower 4500 = 155170924560559531400 := by decide +kernel

theorem logLower_4500_ge_pilot :
    (8411832675757 / 10 ^ 12 : ℝ) ≤ (logLower 4500 : ℝ) / scale := by
  rw [logLower_4500_eval]
  norm_num [scale]

end RosserLogCertificate

-- Source: Solutions/RosserBlockCheck.lean
/-! A single exact integer comparison proves the real bound on a block. -/

namespace RosserBlockCheck

open RosserProductCertificate RosserLogCertificate

def Bound (x : ℝ) : Prop :=
  eulerProduct ⌊x⌋₊ <
    Real.exp Real.eulerMascheroniConstant * Real.log x +
      2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x

theorem check_sound (a b v : ℕ) (ha : 1 ≤ a) (hcheck : check a b v = true)
    (hv : (v : ℝ) / scale ≤ ∏ p ∈ Nat.primesLE b, (((p : ℝ) - 1) / p))
    (x : ℝ) (hax : (a : ℝ) ≤ x) (hxb : x ≤ b) : Bound x := by
  obtain ⟨hv0, hnum⟩ := of_decide_eq_true hcheck
  have hv0' : (0 : ℝ) < v := by exact_mod_cast hv0
  have hD : (0 : ℝ) < scale := by exact_mod_cast scale_pos
  have hS : (0 : ℝ) < sqrtUpper b := by
    exact_mod_cast (show 0 < sqrtUpper b by unfold sqrtUpper; omega)
  have hBS : (b : ℝ) ≤ (sqrtUpper b : ℝ) ^ 2 := by
    have h : b ≤ sqrtUpper b ^ 2 := (Nat.lt_succ_sqrt' b).le
    exact_mod_cast h
  have hineq : (scale : ℝ) * scale * 10 ^ 8 * sqrtUpper b <
      (v : ℝ) * 178107239 * ((logLower a : ℝ) * sqrtUpper b + 2 * scale) := by
    exact_mod_cast hnum
  have hc : (1 : ℝ) / ((v : ℝ) / scale) <
      (178107239 / 10 ^ 8 : ℝ) *
        ((logLower a : ℝ) / scale + 2 / sqrtUpper b) := by
    apply (div_lt_iff₀ (div_pos hv0' hD)).mpr
    field_simp
    nlinarith only [hineq]
  exact block_bound b a x (1 / ((v : ℝ) / scale)) (178107239 / 10 ^ 8)
    ((logLower a : ℝ) / scale) (sqrtUpper b)
    (by exact_mod_cast ha) hax hxb
    (eulerProduct_le_of_reciprocal b _ (div_pos hv0' hD) hv)
    exp_gamma_lower (div_nonneg (Nat.cast_nonneg _) hD.le)
    (logLower_sound a ha) hS hBS hc

end RosserBlockCheck

-- Source: Solutions/AlternativeProductMoments.lean
/-!
A different arithmetic kernel for a finite Euler-product certificate.
It replaces multiplication/division for every prime by three integer moments
per block. This file proves the mathematical inequalities, not the full
Rosser--Schoenfeld bound through 10^8.
-/

namespace AlternativeProductMoments

theorem square_sum_ge_sum_squares (xs : List ℝ)
    (hxs : ∀ x ∈ xs, 0 ≤ x) :
    (xs.map (fun x => x ^ 2)).sum ≤ xs.sum ^ 2 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hxs x (by simp)
    have htail : ∀ y ∈ xs, 0 ≤ y := by
      intro y hy
      exact hxs y (by simp [hy])
    have hs : 0 ≤ xs.sum := List.sum_nonneg htail
    have hi := ih htail
    simp only [List.map_cons, List.sum_cons]
    nlinarith [mul_nonneg hx hs]

/-- A conservative third-order Bonferroni bound. Its induction only uses
the nonnegative first two moments; no exponential or logarithm is needed. -/
theorem product_lower (xs : List ℝ)
    (hxs : ∀ x ∈ xs, 0 ≤ x ∧ x ≤ 1) :
    (1 - xs.sum) * (1 + (xs.sum ^ 2 - (xs.map (fun x => x ^ 2)).sum) / 2) ≤
      (xs.map (fun x => 1 - x)).prod := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hxs x (by simp)
    have htail : ∀ y ∈ xs, 0 ≤ y ∧ y ≤ 1 := by
      intro y hy
      exact hxs y (by simp [hy])
    have hs : 0 ≤ xs.sum := List.sum_nonneg (fun y hy => (htail y hy).1)
    have he : 0 ≤ xs.sum ^ 2 - (xs.map (fun y => y ^ 2)).sum :=
      sub_nonneg.mpr (square_sum_ge_sum_squares xs (fun y hy => (htail y hy).1))
    have hmul := mul_le_mul_of_nonneg_left (ih htail) (sub_nonneg.mpr hx.2)
    have herr : 0 ≤ x * xs.sum *
        ((xs.sum ^ 2 - (xs.map (fun y => y ^ 2)).sum) / 2 + xs.sum + x) := by
      exact mul_nonneg (mul_nonneg hx.1 hs)
        (add_nonneg (add_nonneg (div_nonneg he (by norm_num)) hs) hx.1)
    simp only [List.map_cons, List.sum_cons, List.prod_cons]
    nlinarith only [hmul, herr]

/-- Safe interval versions of the two moments. The max allows blocks with
zero or one candidate, for which the approximate pair correction is negative. -/
theorem product_lower_of_moment_bounds (xs : List ℝ) (L U T : ℝ)
    (hxs : ∀ x ∈ xs, 0 ≤ x ∧ x ≤ 1)
    (hL0 : 0 ≤ L) (hL : L ≤ xs.sum) (hU : xs.sum ≤ U) (hU1 : U ≤ 1)
    (hT : (xs.map (fun x => x ^ 2)).sum ≤ T) :
    (1 - U) * (1 + max 0 ((L ^ 2 - T) / 2)) ≤
      (xs.map (fun x => 1 - x)).prod := by
  have hs : 0 ≤ xs.sum := List.sum_nonneg (fun y hy => (hxs y hy).1)
  have he := square_sum_ge_sum_squares xs (fun y hy => (hxs y hy).1)
  have hpair : max 0 ((L ^ 2 - T) / 2) ≤
      (xs.sum ^ 2 - (xs.map (fun x => x ^ 2)).sum) / 2 := by
    apply max_le
    · linarith
    · nlinarith [sq_nonneg (xs.sum - L)]
  calc
    (1 - U) * (1 + max 0 ((L ^ 2 - T) / 2)) ≤
        (1 - xs.sum) * (1 + (xs.sum ^ 2 - (xs.map (fun x => x ^ 2)).sum) / 2) := by
      apply mul_le_mul
      · linarith
      · linarith
      · positivity
      · linarith
    _ ≤ _ := product_lower xs hxs

/-- The first three terms of the geometric expansion enclose 1/(a+d).
Summing this uses only the count, sum, and sum of squares of integer offsets. -/
theorem inverse_bounds (a d : ℝ) (ha : 0 < a) (hd : 0 ≤ d) :
    1 / a - d / a ^ 2 ≤ 1 / (a + d) ∧
    1 / (a + d) ≤ 1 / a - d / a ^ 2 + d ^ 2 / a ^ 3 := by
  have had : 0 < a + d := by linarith
  constructor
  · apply (le_div_iff₀ had).mpr
    field_simp
    nlinarith [sq_nonneg d]
  · apply (div_le_iff₀ had).mpr
    field_simp
    nlinarith [mul_nonneg hd (sq_nonneg d)]

/-- Moment bounds for all candidates of the form a+d in a block. -/
theorem reciprocal_moment_bounds (a : ℝ) (ds : List ℝ)
    (ha : 0 < a) (hds : ∀ d ∈ ds, 0 ≤ d) :
    ((ds.length : ℝ) / a - ds.sum / a ^ 2 ≤
        (ds.map (fun d => 1 / (a + d))).sum) ∧
    ((ds.map (fun d => 1 / (a + d))).sum ≤
        (ds.length : ℝ) / a - ds.sum / a ^ 2 +
          (ds.map (fun d => d ^ 2)).sum / a ^ 3) ∧
    ((ds.map (fun d => (1 / (a + d)) ^ 2)).sum ≤
        (ds.length : ℝ) / a ^ 2) := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    have hd := hds d (by simp)
    have htail : ∀ e ∈ ds, 0 ≤ e := by
      intro e he
      exact hds e (by simp [he])
    have hi := ih htail
    have hb := inverse_bounds a d ha hd
    have had : 0 < a + d := by linarith
    have hsq : (1 / (a + d)) ^ 2 ≤ 1 / a ^ 2 := by
      rw [div_pow, one_pow]
      apply div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos ha)
      nlinarith [sq_nonneg d, mul_nonneg ha.le hd]
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one,
      List.map_cons, List.sum_cons]
    constructor
    · convert add_le_add hb.1 hi.1 using 1 <;> first | rfl | ring
    constructor
    · convert add_le_add hb.2 hi.2.1 using 1 <;> first | rfl | ring
    · convert add_le_add hsq hi.2.2 using 1 <;> first | rfl | ring

/-- The exact factor used by the alternative experiment. Checking the three
integer moments suffices for the product bound for an entire block. -/
theorem block_factor_lower (a : ℝ) (ds : List ℝ)
    (ha : 1 ≤ a) (hds : ∀ d ∈ ds, 0 ≤ d)
    (hL : 0 ≤ (ds.length : ℝ) / a - ds.sum / a ^ 2)
    (hU : (ds.length : ℝ) / a - ds.sum / a ^ 2 +
      (ds.map (fun d => d ^ 2)).sum / a ^ 3 ≤ 1) :
    (1 - ((ds.length : ℝ) / a - ds.sum / a ^ 2 +
        (ds.map (fun d => d ^ 2)).sum / a ^ 3)) *
      (1 + max 0 ((((ds.length : ℝ) / a - ds.sum / a ^ 2) ^ 2 -
        (ds.length : ℝ) / a ^ 2) / 2)) ≤
      (ds.map (fun d => 1 - 1 / (a + d))).prod := by
  have ha0 : 0 < a := by linarith
  have hb := reciprocal_moment_bounds a ds ha0 hds
  have hxs : ∀ x ∈ ds.map (fun d => 1 / (a + d)), 0 ≤ x ∧ x ≤ 1 := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
    have hd0 := hds d hd
    have had : 0 < a + d := by linarith
    constructor
    · positivity
    · apply (div_le_one had).mpr
      linarith
  simpa only [List.map_map, Function.comp_def] using
    product_lower_of_moment_bounds (ds.map (fun d => 1 / (a + d)))
      ((ds.length : ℝ) / a - ds.sum / a ^ 2)
      ((ds.length : ℝ) / a - ds.sum / a ^ 2 +
        (ds.map (fun d => d ^ 2)).sum / a ^ 3)
      ((ds.length : ℝ) / a ^ 2) hxs hL hb.1 hb.2.1 hU
      (by simpa only [List.map_map, Function.comp_def] using hb.2.2)

private theorem cast_sub_max (n m : ℕ) :
    ((n - m : ℕ) : ℝ) = max 0 ((n : ℝ) - m) := by
  by_cases h : m ≤ n
  · rw [Nat.cast_sub h, max_eq_right]
    exact sub_nonneg.mpr (by exact_mod_cast h)
  · have hmn : n ≤ m := by omega
    rw [Nat.sub_eq_zero_of_le hmn, Nat.cast_zero, max_eq_left]
    exact sub_nonpos.mpr (by exact_mod_cast hmn)

/-- Cast the three integer moments once, outside the computational loop. -/
theorem integer_factor_lower (a : ℕ) (ds : List ℕ)
    (ha : 2 ≤ a) (hfirst : firstMoment ds ≤ ds.length * a)
    (hupper : upperNumerator a ds ≤ a ^ 3) :
    (factorNumerator a ds : ℝ) / factorDenominator a ≤
      (ds.map (fun (d : ℕ) => 1 - 1 / ((a : ℝ) + d))).prod := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have ha_ne : (a : ℝ) ≠ 0 := ne_of_gt ha0
  have hfirst' : a * firstMoment ds ≤ ds.length * a ^ 2 := by
    calc
      a * firstMoment ds ≤ a * (ds.length * a) := Nat.mul_le_mul_left a hfirst
      _ = ds.length * a ^ 2 := by ring
  have hcastL : (lowerNumerator a ds : ℝ) =
      (ds.length : ℝ) * a - firstMoment ds := by
    simp only [lowerNumerator, Nat.cast_sub hfirst, Nat.cast_mul]
  have hcastU : (upperNumerator a ds : ℝ) =
      (ds.length : ℝ) * (a : ℝ) ^ 2 - a * firstMoment ds + secondMoment ds := by
    simp only [upperNumerator, Nat.cast_add, Nat.cast_sub hfirst', Nat.cast_mul,
      Nat.cast_pow]
  have hcastE : (pairNumerator a ds : ℝ) =
      max 0 (((ds.length : ℝ) * a - firstMoment ds) ^ 2 -
        (ds.length : ℝ) * (a : ℝ) ^ 2) := by
    simp only [pairNumerator, cast_sub_max, Nat.cast_pow, Nat.cast_mul, hcastL]
  have hL : 0 ≤ (ds.length : ℝ) / a - (firstMoment ds : ℝ) / (a : ℝ) ^ 2 := by
    have heq : (ds.length : ℝ) / a - (firstMoment ds : ℝ) / (a : ℝ) ^ 2 =
        (lowerNumerator a ds : ℝ) / (a : ℝ) ^ 2 := by
      rw [hcastL]
      field_simp
    rw [heq]
    positivity
  have hU : (ds.length : ℝ) / a - (firstMoment ds : ℝ) / (a : ℝ) ^ 2 +
      (secondMoment ds : ℝ) / (a : ℝ) ^ 3 ≤ 1 := by
    have hcast := (show (upperNumerator a ds : ℝ) ≤ (a : ℝ) ^ 3 by exact_mod_cast hupper)
    have heq : (ds.length : ℝ) / a - (firstMoment ds : ℝ) / (a : ℝ) ^ 2 +
        (secondMoment ds : ℝ) / (a : ℝ) ^ 3 =
        (upperNumerator a ds : ℝ) / (a : ℝ) ^ 3 := by
      rw [hcastU]
      field_simp
    rw [heq]
    exact (div_le_one (pow_pos ha0 3)).mpr hcast
  have hsum : (ds.map (fun (d : ℕ) => (d : ℝ))).sum = (firstMoment ds : ℝ) := by
    simp only [firstMoment, Nat.cast_list_sum]
  have hsquares :
      ((ds.map (fun (d : ℕ) => (d : ℝ))).map (fun d => d ^ 2)).sum =
        (secondMoment ds : ℝ) := by
    simp only [secondMoment, Nat.cast_list_sum, List.map_map, Function.comp_def,
      Nat.cast_pow]
  have hsquares' : (ds.map (fun (d : ℕ) => (d : ℝ) ^ 2)).sum =
      (secondMoment ds : ℝ) := by
    simpa only [List.map_map, Function.comp_def] using hsquares
  have hb := block_factor_lower (a : ℝ) (ds.map (fun (d : ℕ) => (d : ℝ)))
    (by exact_mod_cast (show 1 ≤ a by omega))
    (by intro d hd; obtain ⟨n, _, rfl⟩ := List.mem_map.mp hd; positivity)
    (by simpa only [List.length_map, hsum] using hL)
    (by simpa only [List.length_map, hsum, hsquares] using hU)
  simp only [List.length_map, hsum, List.map_map, Function.comp_def, hsquares'] at hb
  have hpair : (pairNumerator a ds : ℝ) / (2 * (a : ℝ) ^ 4) =
      max 0 ((((ds.length : ℝ) / a - (firstMoment ds : ℝ) / (a : ℝ) ^ 2) ^ 2 -
        (ds.length : ℝ) / (a : ℝ) ^ 2) / 2) := by
    rw [hcastE, ← max_div_div_right (by positivity : (0 : ℝ) ≤ 2 * (a : ℝ) ^ 4),
      zero_div]
    congr 1
    field_simp
  have hfactor : (factorNumerator a ds : ℝ) / factorDenominator a =
      (1 - ((ds.length : ℝ) / a - (firstMoment ds : ℝ) / (a : ℝ) ^ 2 +
        (secondMoment ds : ℝ) / (a : ℝ) ^ 3)) *
        (1 + max 0 ((((ds.length : ℝ) / a - (firstMoment ds : ℝ) / (a : ℝ) ^ 2) ^ 2 -
          (ds.length : ℝ) / (a : ℝ) ^ 2) / 2)) := by
    rw [← hpair]
    simp only [factorNumerator, factorDenominator, Nat.cast_mul,
      Nat.cast_sub hupper, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat, hcastU]
    field_simp
  rw [hfactor]
  exact hb

/-- The complete integer step: all candidates may be composite and all
computations are on natural numbers. A separate sieve coverage theorem
relates their product to the actual prime product. -/
theorem momentStep_sound (D v a : ℕ) (ds : List ℕ) (Q : ℝ)
    (hD : 0 < D) (ha : 2 ≤ a) (hfirst : firstMoment ds ≤ ds.length * a)
    (hupper : upperNumerator a ds ≤ a ^ 3) (hv : (v : ℝ) / D ≤ Q) :
    (momentStep v a ds : ℝ) / D ≤
      Q * (ds.map (fun (d : ℕ) => 1 - 1 / ((a : ℝ) + d))).prod := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have hQ : 0 ≤ Q := (by positivity : (0 : ℝ) ≤ (v : ℝ) / D).trans hv
  have hround : (momentStep v a ds : ℝ) ≤
      (v : ℝ) * (factorNumerator a ds : ℝ) / factorDenominator a := by
    simpa only [momentStep, Nat.cast_mul] using
      (Nat.cast_div_le (m := v * factorNumerator a ds)
        (n := factorDenominator a) (α := ℝ))
  calc
    (momentStep v a ds : ℝ) / D ≤
        ((v : ℝ) * (factorNumerator a ds : ℝ) / factorDenominator a) / D :=
      div_le_div_of_nonneg_right hround hD0.le
    _ = ((v : ℝ) / D) * ((factorNumerator a ds : ℝ) / factorDenominator a) := by ring
    _ ≤ Q * ((factorNumerator a ds : ℝ) / factorDenominator a) :=
      mul_le_mul_of_nonneg_right hv (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left (integer_factor_lower a ds ha hfirst hupper) hQ

end AlternativeProductMoments

-- Source: Solutions/RosserMomentBridge.lean
/-!
Connect a rounded moment update to the genuine reciprocal prime product.
The candidate list only needs to cover all primes in the block; it may also
contain composites. Its correctness is separate from the arithmetic update.
-/

namespace RosserMomentBridge

open AlternativeProductMoments

noncomputable def reciprocalProduct (n : ℕ) : ℝ :=
  ∏ p ∈ Nat.primesLE n, (((p : ℝ) - 1) / p)

theorem reciprocalProduct_nonneg (n : ℕ) : 0 ≤ reciprocalProduct n := by
  apply Finset.prod_nonneg
  intro p hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast Nat.two_le_of_mem_primesLE hp
  exact div_nonneg (by linarith) (by linarith)

/-- The list product bounds the product over new primes in (a,b]. -/
theorem candidate_product_le_prime_block (a b : ℕ) (ds : List ℕ)
    (ha : 2 ≤ a) (hds : ds.Nodup)
    (hbounds : ∀ d ∈ ds, 0 < d ∧ d ≤ b - a)
    (hcover : ∀ p : ℕ, Nat.Prime p → a < p → p ≤ b → p - a ∈ ds) :
    (ds.map (fun (d : ℕ) => 1 - 1 / ((a : ℝ) + d))).prod ≤
      ∏ p ∈ Nat.primesLE b \ Nat.primesLE a, (((p : ℝ) - 1) / p) := by
  let ps := ds.map (fun (d : ℕ) => a + d)
  have hps : ps.Nodup := List.Nodup.map (by intro x y h; dsimp at h; omega) hds
  have hps_bounds : ∀ p ∈ ps.toFinset, a < p ∧ p ≤ b := by
    intro p hp
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hp)
    have hb := hbounds d hd
    omega
  have hsubset : Nat.primesLE b \ Nat.primesLE a ⊆ ps.toFinset := by
    intro p hp
    obtain ⟨hpb, hpa⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hpb', hpprime⟩ := Nat.mem_primesLE.mp hpb
    have hap : a < p := by
      by_contra h
      exact hpa (Nat.mem_primesLE.mpr ⟨by omega, hpprime⟩)
    apply List.mem_toFinset.mpr
    exact List.mem_map.mpr ⟨p - a, hcover p hpprime hap hpb', by omega⟩
  have hbound := RosserProductCertificate.reciprocal_product_of_superset
    (Nat.primesLE b \ Nat.primesLE a) ps.toFinset hsubset
    (by intro p hp; have h := hps_bounds p hp; omega)
  have hprod :
      (∏ p ∈ ps.toFinset, (((p : ℝ) - 1) / p)) =
        (ds.map (fun (d : ℕ) => 1 - 1 / ((a : ℝ) + d))).prod := by
    rw [List.prod_toFinset _ hps]
    change ((ds.map (fun (d : ℕ) => a + d)).map
      (fun (p : ℕ) => ((p : ℝ) - 1) / p)).prod = _
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro d _
    have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
    have had : (0 : ℝ) < a + d := by positivity
    simp only [Function.comp_def, Nat.cast_add]
    field_simp
  rwa [hprod] at hbound

/-- A verified update of the reciprocal product across one whole block.
Every prime in (a,b] must survive the candidate sieve. Extra composite
candidates are harmless because their factors lie between zero and one. -/
theorem momentStep_reciprocalProduct (D v a b : ℕ) (ds : List ℕ)
    (hD : 0 < D) (hab : a ≤ b) (ha : 2 ≤ a) (hds : ds.Nodup)
    (hbounds : ∀ d ∈ ds, 0 < d ∧ d ≤ b - a)
    (hcover : ∀ p : ℕ, Nat.Prime p → a < p → p ≤ b → p - a ∈ ds)
    (hfirst : firstMoment ds ≤ ds.length * a)
    (hupper : upperNumerator a ds ≤ a ^ 3)
    (hv : (v : ℝ) / D ≤ reciprocalProduct a) :
    (momentStep v a ds : ℝ) / D ≤ reciprocalProduct b := by
  have hstep := momentStep_sound D v a ds (reciprocalProduct a)
    hD ha hfirst hupper hv
  have hblock := candidate_product_le_prime_block a b ds ha hds hbounds hcover
  have hsplit :
      reciprocalProduct a *
        (∏ p ∈ Nat.primesLE b \ Nat.primesLE a, (((p : ℝ) - 1) / p)) =
        reciprocalProduct b := by
    unfold reciprocalProduct
    rw [mul_comm]
    exact Finset.prod_sdiff (Nat.primesLE_mono hab)
  calc
    (momentStep v a ds : ℝ) / D ≤
        reciprocalProduct a * (ds.map (fun (d : ℕ) => 1 - 1 / ((a : ℝ) + d))).prod :=
      hstep
    _ ≤ reciprocalProduct a *
        (∏ p ∈ Nat.primesLE b \ Nat.primesLE a, (((p : ℝ) - 1) / p)) :=
      mul_le_mul_of_nonneg_left hblock (reciprocalProduct_nonneg a)
    _ = reciprocalProduct b := hsplit

end RosserMomentBridge

-- Source: Solutions/RosserBernoulli.lean
/-! An elementary lower bound for the product of prime factors in a block. -/

namespace RosserBernoulli

theorem one_sub_sum_le_prod {α : Type*} (s : Finset α) (u : α → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ u i) (h1 : ∀ i ∈ s, u i ≤ 1) :
    1 - ∑ i ∈ s, u i ≤ ∏ i ∈ s, (1 - u i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hui0 : 0 ≤ u i := h0 i (Finset.mem_insert_self _ _)
    have hui1 : u i ≤ 1 := h1 i (Finset.mem_insert_self _ _)
    have htail0 : ∀ j ∈ s, 0 ≤ u j := by
      intro j hj
      exact h0 j (Finset.mem_insert_of_mem hj)
    have htail1 : ∀ j ∈ s, u j ≤ 1 := by
      intro j hj
      exact h1 j (Finset.mem_insert_of_mem hj)
    have hs0 : 0 ≤ ∑ j ∈ s, u j := Finset.sum_nonneg htail0
    have htail := ih htail0 htail1
    have hmul := mul_le_mul_of_nonneg_left htail (by linarith : 0 ≤ 1 - u i)
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    nlinarith only [hmul, hui0, hs0]

theorem prime_block_lower (a n k : ℕ) (ha : 2 ≤ a) (han : a ≤ n)
    (hcard : (Nat.primesLE n \ Nat.primesLE a).card ≤ k) :
    1 - (k : ℝ) / (a + 1) ≤
      ∏ p ∈ Nat.primesLE n \ Nat.primesLE a, (((p : ℝ) - 1) / p) := by
  let s := Nat.primesLE n \ Nat.primesLE a
  have hpa : ∀ p ∈ s, a < p := by
    intro p hp
    have hp' := Finset.mem_sdiff.mp hp
    have hprime := (Nat.mem_primesLE.mp hp'.1).2
    by_contra h
    exact hp'.2 (Nat.mem_primesLE.mpr ⟨by omega, hprime⟩)
  have hp2 : ∀ p ∈ s, (2 : ℝ) ≤ p := by
    intro p hp
    exact_mod_cast (show 2 ≤ p by have := hpa p hp; omega)
  have h0 : ∀ p ∈ s, (0 : ℝ) ≤ 1 / p := by
    intro p hp
    positivity
  have h1 : ∀ p ∈ s, (1 : ℝ) / p ≤ 1 := by
    intro p hp
    have h := hp2 p hp
    apply (div_le_iff₀ (by linarith : (0 : ℝ) < p)).mpr
    linarith
  have hpoint : ∀ p ∈ s, (1 : ℝ) / p ≤ 1 / (a + 1) := by
    intro p hp
    have h := hpa p hp
    have h' : (a + 1 : ℝ) ≤ p := by exact_mod_cast h
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) h'
  have hsum : (∑ p ∈ s, (1 : ℝ) / p) ≤ (k : ℝ) / (a + 1) := by
    calc
      (∑ p ∈ s, (1 : ℝ) / p) ≤ ∑ _p ∈ s, (1 : ℝ) / (a + 1) :=
        Finset.sum_le_sum hpoint
      _ = (s.card : ℝ) / (a + 1) := by simp [div_eq_mul_inv]
      _ ≤ (k : ℝ) / (a + 1) :=
        div_le_div_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
  have hb := one_sub_sum_le_prod s (fun p => (1 : ℝ) / p) h0 h1
  have heq : (∏ p ∈ s, (1 - (1 : ℝ) / p)) =
      ∏ p ∈ s, (((p : ℝ) - 1) / p) := by
    apply Finset.prod_congr rfl
    intro p hp
    have hp0 : (0 : ℝ) < p := by have := hp2 p hp; linarith
    field_simp
    <;> ring
  calc
    1 - (k : ℝ) / (a + 1) ≤ 1 - ∑ p ∈ s, (1 : ℝ) / p := by linarith only [hsum]
    _ ≤ ∏ p ∈ s, (1 - (1 : ℝ) / p) := hb
    _ = _ := heq

theorem reciprocal_prefix_lower (a n k : ℕ) (ha : 2 ≤ a) (han : a ≤ n)
    (hcard : (Nat.primesLE n \ Nat.primesLE a).card ≤ k) :
    RosserMomentBridge.reciprocalProduct a * (1 - (k : ℝ) / (a + 1)) ≤
      RosserMomentBridge.reciprocalProduct n := by
  have hblock := prime_block_lower a n k ha han hcard
  have hnonneg := RosserMomentBridge.reciprocalProduct_nonneg a
  have hmul := mul_le_mul_of_nonneg_left hblock hnonneg
  have hsplit : RosserMomentBridge.reciprocalProduct a *
      (∏ p ∈ Nat.primesLE n \ Nat.primesLE a, (((p : ℝ) - 1) / p)) =
      RosserMomentBridge.reciprocalProduct n := by
    unfold RosserMomentBridge.reciprocalProduct
    rw [mul_comm]
    exact Finset.prod_sdiff (Nat.primesLE_mono han)
  exact hmul.trans_eq hsplit

end RosserBernoulli

-- Source: Solutions/RosserPrefixBounds.lean
/-! Elementary interval bounds for the fast finite Rosser certificate. -/

namespace RosserPrefixBounds

theorem log_step (a b x : ℝ) (ha : 0 < a) (hax : a ≤ x) (hxb : x ≤ b) :
    (x - a) / b ≤ Real.log x - Real.log a := by
  have hx : 0 < x := lt_of_lt_of_le ha hax
  have hb : 0 < b := lt_of_lt_of_le hx hxb
  have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hx ha)
  rw [Real.log_div (ne_of_gt hx) (ne_of_gt ha)] at hlog
  have heq : 1 - (x / a)⁻¹ = (x - a) / x := by
    field_simp
  rw [heq] at hlog
  exact (div_le_div_of_nonneg_left (sub_nonneg.mpr hax) hx hxb).trans hlog

theorem sqrt_reciprocal_step (a x : ℝ) (ha : 0 < a) (hax : a ≤ x) :
    -(x - a) / (a * Real.sqrt a) ≤
      2 / Real.sqrt x - 2 / Real.sqrt a := by
  let s := Real.sqrt x
  let t := Real.sqrt a
  have hx : 0 < x := lt_of_lt_of_le ha hax
  have hs : 0 < s := Real.sqrt_pos.mpr hx
  have ht : 0 < t := Real.sqrt_pos.mpr ha
  have hst : t ≤ s := Real.sqrt_le_sqrt hax
  have hsa : s ^ 2 = x := Real.sq_sqrt hx.le
  have hta : t ^ 2 = a := Real.sq_sqrt ha.le
  have hden : 2 * a * t ≤ s * t * (s + t) := by
    have hfactor : 0 ≤ t * (s - t) * (s + 2 * t) := by positivity
    calc
      2 * a * t = 2 * t ^ 3 := by rw [← hta]; ring
      _ ≤ s * t * (s + t) := by nlinarith only [hfactor]
  have hdenpos : 0 < s * t * (s + t) := by positivity
  have hatpos : 0 < a * t := by positivity
  have hfrac : 2 / (s * t * (s + t)) ≤ 1 / (a * t) := by
    apply (div_le_div_iff₀ hdenpos hatpos).mpr
    nlinarith only [hden]
  have hmul := mul_le_mul_of_nonneg_right hfrac (sub_nonneg.mpr hax)
  have hidentity : 2 / t - 2 / s =
      (x - a) * (2 / (s * t * (s + t))) := by
    rw [← hsa, ← hta]
    field_simp
    <;> ring
  have hnegative : -(x - a) * (1 / (a * t)) ≤
      -(x - a) * (2 / (s * t * (s + t))) := by
    simpa only [neg_mul, mul_comm] using neg_le_neg hmul
  calc
    -(x - a) / (a * Real.sqrt a) = -(x - a) * (1 / (a * t)) := by
      dsimp [t]; ring
    _ ≤ -(x - a) * (2 / (s * t * (s + t))) := hnegative
    _ = -((x - a) * (2 / (s * t * (s + t)))) := by ring
    _ = -(2 / t - 2 / s) := by rw [← hidentity]
    _ = 2 / s - 2 / t := by ring
    _ = 2 / Real.sqrt x - 2 / Real.sqrt a := rfl

theorem log_sqrt_linear (a b x : ℝ) (ha : 0 < a) (hax : a ≤ x) (hxb : x ≤ b) :
    Real.log a + 2 / Real.sqrt a +
        (1 / b - 1 / (a * Real.sqrt a)) * (x - a) ≤
      Real.log x + 2 / Real.sqrt x := by
  have hlog := log_step a b x ha hax hxb
  have hsqrt := sqrt_reciprocal_step a x ha hax
  simp only [neg_div] at hsqrt
  calc
    Real.log a + 2 / Real.sqrt a +
        (1 / b - 1 / (a * Real.sqrt a)) * (x - a) =
      Real.log a + 2 / Real.sqrt a +
        (x - a) / b - (x - a) / (a * Real.sqrt a) := by ring
    _ ≤ Real.log x + 2 / Real.sqrt x := by linarith only [hlog, hsqrt]

theorem reciprocal_barrier_chord (A U B C h d : ℝ)
    (hA : 0 ≤ A) (hU : 0 ≤ U) (hB : 0 < B) (hC : 0 ≤ C)
    (hd : 0 ≤ d) (hdh : d ≤ h) :
    A * (1 - U / B) + A * U * C / (B * (B + C * h)) * d ≤
      A * (1 - U / (B + C * d)) := by
  have hh : 0 ≤ h := le_trans hd hdh
  have hbh : 0 < B + C * h := by positivity
  have hbd : 0 < B + C * d := by positivity
  have hhd : 0 ≤ h - d := sub_nonneg.mpr hdh
  have hnum : 0 ≤ A * U * C ^ 2 * d * (h - d) := by positivity
  have hden : 0 < B * (B + C * d) * (B + C * h) := by positivity
  have hid :
      A * (1 - U / (B + C * d)) -
        (A * (1 - U / B) + A * U * C / (B * (B + C * h)) * d) =
      (A * U * C ^ 2 * d * (h - d)) /
        (B * (B + C * d) * (B + C * h)) := by
    field_simp
    <;> ring
  have hnonneg := div_nonneg hnum hden.le
  linarith only [hid, hnonneg]

/-- A lower affine envelope for the full real-valued target on an interval. -/
theorem target_linear_lower (a b x g B C : ℝ)
    (ha : 0 < a) (hax : a ≤ x) (hxb : x ≤ b)
    (hg : 0 ≤ g) (hgamma : g ≤ Real.exp Real.eulerMascheroniConstant)
    (hB : B ≤ g * (Real.log a + 2 / Real.sqrt a))
    (hC : C ≤ g * (1 / b - 1 / (a * Real.sqrt a)))
    (hFx : 0 ≤ Real.log x + 2 / Real.sqrt x) :
    B + C * (x - a) ≤
      Real.exp Real.eulerMascheroniConstant *
        (Real.log x + 2 / Real.sqrt x) := by
  have hd : 0 ≤ x - a := sub_nonneg.mpr hax
  have hlin := log_sqrt_linear a b x ha hax hxb
  have hC' := mul_le_mul_of_nonneg_right hC hd
  have hlin' := mul_le_mul_of_nonneg_left hlin hg
  have hgamma' := mul_le_mul_of_nonneg_right hgamma hFx
  nlinarith only [hB, hC', hlin', hgamma']

/-- Integer square-root bounds may be used with opposite rounding directions
in the intercept and the slope. -/
theorem rounded_target_linear_lower (a b x g L r S : ℝ)
    (ha : 1 ≤ a) (hax : a ≤ x) (hxb : x ≤ b)
    (hg : 0 ≤ g) (hgamma : g ≤ Real.exp Real.eulerMascheroniConstant)
    (hL : L ≤ Real.log a) (hr : 0 < r) (hrS : r ≤ Real.sqrt a)
    (hS : 0 < S) (hSa : Real.sqrt a ≤ S) :
    g * (L + 2 / S) +
      g * (1 / b - 1 / (a * r)) * (x - a) ≤
      Real.exp Real.eulerMascheroniConstant *
        (Real.log x + 2 / Real.sqrt x) := by
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr (by linarith)
  have hSdiv : 2 / S ≤ 2 / Real.sqrt a :=
    div_le_div_of_nonneg_left (by norm_num) hsa hSa
  have hB : g * (L + 2 / S) ≤
      g * (Real.log a + 2 / Real.sqrt a) := by
    apply mul_le_mul_of_nonneg_left _ hg
    linarith only [hL, hSdiv]
  have har : 0 < a * r := mul_pos (by linarith) hr
  have hsar : a * r ≤ a * Real.sqrt a :=
    mul_le_mul_of_nonneg_left hrS (by linarith)
  have hRdiv : 1 / (a * Real.sqrt a) ≤ 1 / (a * r) :=
    div_le_div_of_nonneg_left (by norm_num) har hsar
  have hC : g * (1 / b - 1 / (a * r)) ≤
      g * (1 / b - 1 / (a * Real.sqrt a)) := by
    apply mul_le_mul_of_nonneg_left _ hg
    linarith only [hRdiv]
  have hx1 : (1 : ℝ) ≤ x := ha.trans hax
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
  have hFx : 0 ≤ Real.log x + 2 / Real.sqrt x := by positivity
  exact target_linear_lower a b x g _ _ (by linarith) hax hxb hg
    hgamma hB hC hFx

/-- A strict count bound in a prefix converts a reciprocal-product lower
bound into a strict upper bound on the Euler product. -/
theorem prefix_count_to_product (a n k : ℕ) (q T : ℝ)
    (ha : 2 ≤ a) (han : a ≤ n) (hq : 0 < q) (hT : 0 < T)
    (hv : q ≤ RosserMomentBridge.reciprocalProduct a)
    (hcard : (Nat.primesLE n \ Nat.primesLE a).card ≤ k)
    (hcount : (k : ℝ) < (a + 1) * (1 - (1 / q) / T)) :
    RosserProductCertificate.eulerProduct n < T := by
  let A : ℝ := a + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have hfrac : (k : ℝ) / A < 1 - (1 / q) / T := by
    apply (div_lt_iff₀ hA).mpr
    dsimp [A] at hcount ⊢
    nlinarith only [hcount]
  have hfactor : 0 < 1 - (k : ℝ) / A := by
    have : 0 < (1 / q) / T := by positivity
    linarith only [hfrac, this]
  have hqprod : q * (1 - (k : ℝ) / A) ≤
      RosserMomentBridge.reciprocalProduct n := by
    have hmul := mul_le_mul_of_nonneg_right hv hfactor.le
    exact hmul.trans (by simpa only [A] using
      RosserBernoulli.reciprocal_prefix_lower a n k ha han hcard)
  have hbar : 1 < T * (q * (1 - (k : ℝ) / A)) := by
    have hqt : 0 < q * T := mul_pos hq hT
    have hrewrite : (1 / q) / T = 1 / (q * T) := by ring
    rw [hrewrite] at hfrac
    have h : 1 < (1 - (k : ℝ) / A) * (q * T) :=
      (div_lt_iff₀ hqt).mp (by linarith only [hfrac])
    nlinarith only [h]
  have hr : 0 < q * (1 - (k : ℝ) / A) := mul_pos hq hfactor
  have hupper := RosserProductCertificate.eulerProduct_le_of_reciprocal n
    _ hr hqprod
  have hstrict : 1 / (q * (1 - (k : ℝ) / A)) < T :=
    (div_lt_iff₀ hr).mpr (by nlinarith only [hbar])
  exact hupper.trans_lt hstrict

/-- A certified affine count bound at any point of a block suffices for the
prime product at that point. -/
theorem affine_prefix_to_product (a n k : ℕ) (q B C h d I M : ℝ)
    (ha : 2 ≤ a) (han : a ≤ n) (hq : 0 < q) (hB : 0 < B)
    (hC : 0 ≤ C) (hd : 0 ≤ d) (hdh : d ≤ h)
    (hv : q ≤ RosserMomentBridge.reciprocalProduct a)
    (hcard : (Nat.primesLE n \ Nat.primesLE a).card ≤ k)
    (hI : I ≤ (a + 1) * (1 - (1 / q) / B))
    (hM : M ≤ (a + 1) * (1 / q) * C / (B * (B + C * h)))
    (hk : (k : ℝ) < I + M * d) :
    RosserProductCertificate.eulerProduct n < B + C * d := by
  have hT : 0 < B + C * d := by positivity
  have hchord := reciprocal_barrier_chord (a + 1 : ℝ) (1 / q) B C h d
    (by positivity) (by positivity) hB hC hd hdh
  have hMd := mul_le_mul_of_nonneg_right hM hd
  have hbound : (k : ℝ) < (a + 1) * (1 - (1 / q) / (B + C * d)) := by
    linarith only [hk, hI, hMd, hchord]
  exact prefix_count_to_product a n k q (B + C * d)
    ha han hq hT hv hcard hbound

end RosserPrefixBounds

-- Source: Solutions/RosserPrefixParams.lean
/-! Exact arithmetic for the downward-rounded affine barrier parameters. -/

namespace RosserPrefixParams

open RosserLogCertificate

private theorem forceNat_eq {α : Type} (n : ℕ) (f : ℕ → α) :
    RosserScan.forceNat n f = f n := by
  cases n <;> rfl

structure Parameters where
  intercept : ℕ
  slope : ℕ
  valid : Bool

def parameters (a b v : ℕ) : Parameters :=
  RosserScan.forceNat (Nat.sqrt a) fun r =>
  RosserScan.forceNat (178107239 * (logLower a * (r + 1) + 2 * scale)) fun bn =>
  RosserScan.forceNat (10 ^ 8 * scale * (r + 1)) fun bd =>
  RosserScan.forceNat (178107239 * (a * r - b)) fun cn =>
  RosserScan.forceNat (10 ^ 8 * b * a * r) fun cd =>
    ⟨16384 * (a + 1) * (v * bn - scale * bd) / (v * bn),
     16384 * (a + 1) * scale * cn * bd ^ 2 /
       (v * bn * (bn * cd + cn * bd * (b - a))),
     decide (4500 ≤ a ∧ a < b ∧ b ≤ 10 ^ 8 ∧ 0 < v ∧
       b < a * r ∧ scale * bd < v * bn)⟩

theorem parameters_valid (a b v : ℕ) (h : (parameters a b v).valid = true) :
    4500 ≤ a ∧ a < b ∧ b ≤ 10 ^ 8 ∧ 0 < v ∧
      b < a * Nat.sqrt a ∧
      scale * (10 ^ 8 * scale * (Nat.sqrt a + 1)) <
        v * (178107239 *
          (logLower a * (Nat.sqrt a + 1) + 2 * scale)) := by
  simpa only [parameters, forceNat_eq, decide_eq_true_eq] using h

theorem sqrt_bracket (a : ℕ) (ha : 1 ≤ a) :
    0 < (Nat.sqrt a : ℝ) ∧
      (Nat.sqrt a : ℝ) ≤ Real.sqrt a ∧
      Real.sqrt a ≤ (Nat.sqrt a + 1 : ℕ) := by
  have hr1 : 1 ≤ Nat.sqrt a := by
    apply Nat.le_sqrt.mpr
    simpa using ha
  have hr0 : (0 : ℝ) < Nat.sqrt a := by exact_mod_cast hr1
  have hlow : (Nat.sqrt a : ℝ) ^ 2 ≤ a := by
    exact_mod_cast Nat.sqrt_le' a
  have hhigh : (a : ℝ) ≤ (Nat.sqrt a + 1 : ℕ) ^ 2 := by
    exact_mod_cast (Nat.lt_succ_sqrt' a).le
  exact ⟨hr0, Real.le_sqrt_of_sq_le hlow,
    Real.sqrt_le_iff.mpr ⟨by positivity, hhigh⟩⟩

theorem intercept_lower (J A D v bn bd : ℕ)
    (hJ : 0 < J) (hv : 0 < v) (hbn : 0 < bn) (hbd : 0 < bd)
    (hsub : D * bd ≤ v * bn) :
    ((J * A * (v * bn - D * bd) / (v * bn) : ℕ) : ℝ) / J ≤
      (A : ℝ) * (1 - ((D : ℝ) / v) / ((bn : ℝ) / bd)) := by
  have hJ' : (0 : ℝ) < J := by exact_mod_cast hJ
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  have hbn' : (0 : ℝ) < bn := by exact_mod_cast hbn
  have hbd' : (0 : ℝ) < bd := by exact_mod_cast hbd
  have hsub' : ((v * bn - D * bd : ℕ) : ℝ) =
      (v : ℝ) * bn - D * bd := by
    rw [Nat.cast_sub hsub]
    push_cast
    ring
  have hround := Nat.cast_div_le
    (m := J * A * (v * bn - D * bd)) (n := v * bn) (α := ℝ)
  have heq :
      (((J * A * (v * bn - D * bd) : ℕ) : ℝ) / (v * bn : ℕ)) / J =
        (A : ℝ) * (1 - ((D : ℝ) / v) / ((bn : ℝ) / bd)) := by
    rw [Nat.cast_mul, Nat.cast_mul, hsub', Nat.cast_mul]
    field_simp
    <;> ring
  calc
    ((J * A * (v * bn - D * bd) / (v * bn) : ℕ) : ℝ) / J ≤
        (((J * A * (v * bn - D * bd) : ℕ) : ℝ) / (v * bn : ℕ)) / J :=
      div_le_div_of_nonneg_right hround hJ'.le
    _ = _ := heq

theorem slope_lower (J A D v bn bd cn cd h : ℕ)
    (hJ : 0 < J) (hv : 0 < v) (hbn : 0 < bn) (hbd : 0 < bd)
    (hcd : 0 < cd) :
    ((J * A * D * cn * bd ^ 2 /
        (v * bn * (bn * cd + cn * bd * h)) : ℕ) : ℝ) / J ≤
      (A : ℝ) * ((D : ℝ) / v) * ((cn : ℝ) / cd) /
        (((bn : ℝ) / bd) *
          ((bn : ℝ) / bd + ((cn : ℝ) / cd) * h)) := by
  have hJ' : (0 : ℝ) < J := by exact_mod_cast hJ
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  have hbn' : (0 : ℝ) < bn := by exact_mod_cast hbn
  have hbd' : (0 : ℝ) < bd := by exact_mod_cast hbd
  have hcd' : (0 : ℝ) < cd := by exact_mod_cast hcd
  have hden : 0 < v * bn * (bn * cd + cn * bd * h) := by
    have hterm : 0 < bn * cd := Nat.mul_pos hbn hcd
    positivity
  have hround := Nat.cast_div_le
    (m := J * A * D * cn * bd ^ 2)
    (n := v * bn * (bn * cd + cn * bd * h)) (α := ℝ)
  have heq :
      (((J * A * D * cn * bd ^ 2 : ℕ) : ℝ) /
        (v * bn * (bn * cd + cn * bd * h) : ℕ)) / J =
      (A : ℝ) * ((D : ℝ) / v) * ((cn : ℝ) / cd) /
        (((bn : ℝ) / bd) *
          ((bn : ℝ) / bd + ((cn : ℝ) / cd) * h)) := by
    push_cast
    field_simp
    <;> ring
  calc
    ((J * A * D * cn * bd ^ 2 /
        (v * bn * (bn * cd + cn * bd * h)) : ℕ) : ℝ) / J ≤
      (((J * A * D * cn * bd ^ 2 : ℕ) : ℝ) /
        (v * bn * (bn * cd + cn * bd * h) : ℕ)) / J :=
      div_le_div_of_nonneg_right hround hJ'.le
    _ = _ := heq

theorem intercept_value (D a r ell : ℕ) (hD : 0 < D) :
    ((178107239 * (ell * (r + 1) + 2 * D) : ℕ) : ℝ) /
        (10 ^ 8 * D * (r + 1) : ℕ) =
      (178107239 / 10 ^ 8 : ℝ) *
        ((ell : ℝ) / D + 2 / (r + 1)) := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hr' : (0 : ℝ) < r + 1 := by positivity
  push_cast
  field_simp
  <;> ring

theorem slope_value (a b r : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (hbar : b ≤ a * r) :
    ((178107239 * (a * r - b) : ℕ) : ℝ) /
        (10 ^ 8 * b * a * r : ℕ) =
      (178107239 / 10 ^ 8 : ℝ) *
        (1 / b - 1 / ((a : ℝ) * r)) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hbar]
  push_cast
  field_simp
  <;> ring

theorem parameters_intercept_lower (a b v : ℕ)
    (hvalid : (parameters a b v).valid = true) :
    ((parameters a b v).intercept : ℝ) / 16384 ≤
      (a + 1 : ℝ) *
        (1 - (1 / ((v : ℝ) / scale)) /
          ((178107239 / 10 ^ 8 : ℝ) *
            ((logLower a : ℝ) / scale +
              2 / (Nat.sqrt a + 1 : ℕ)))) := by
  rcases parameters_valid a b v hvalid with
    ⟨ha, hab, hbound, hv, hbar, hnum⟩
  let r := Nat.sqrt a
  let bn := 178107239 * (logLower a * (r + 1) + 2 * scale)
  let bd := 10 ^ 8 * scale * (r + 1)
  have hbn : 0 < bn := by
    dsimp [bn]
    have h2 : 0 < 2 * scale := Nat.mul_pos (by decide) scale_pos
    exact Nat.mul_pos (by decide) (by omega)
  have hbd : 0 < bd := by
    dsimp [bd]
    exact Nat.mul_pos (Nat.mul_pos (by norm_num) scale_pos) (by omega)
  have hnum' : scale * bd ≤ v * bn := by
    simpa only [bn, bd, r] using hnum.le
  have hi := intercept_lower 16384 (a + 1) scale v bn bd
    (by norm_num) hv hbn hbd hnum'
  have hbnval : ((bn : ℝ) / bd) =
      (178107239 / 10 ^ 8 : ℝ) *
        ((logLower a : ℝ) / scale + 2 / (r + 1 : ℕ)) :=
    by simpa only [bn, bd, Nat.cast_add, Nat.cast_one] using
      intercept_value scale a r (logLower a) scale_pos
  have hq : (1 : ℝ) / ((v : ℝ) / scale) = (scale : ℝ) / v := by
    have hv' : (0 : ℝ) < v := by exact_mod_cast hv
    have hD' : (0 : ℝ) < scale := by exact_mod_cast scale_pos
    field_simp
  change ((parameters a b v).intercept : ℝ) / 16384 ≤
    (a + 1 : ℝ) *
      (1 - (1 / ((v : ℝ) / scale)) /
        ((178107239 / 10 ^ 8 : ℝ) *
          ((logLower a : ℝ) / scale + 2 / (r + 1 : ℕ))))
  rw [hq, ← hbnval]
  simpa only [parameters, forceNat_eq, Nat.cast_add, Nat.cast_one,
    Nat.cast_ofNat, r, bn, bd] using hi

theorem parameters_slope_lower (a b v : ℕ)
    (hvalid : (parameters a b v).valid = true) :
    ((parameters a b v).slope : ℝ) / 16384 ≤
      (a + 1 : ℝ) * (1 / ((v : ℝ) / scale)) *
        ((178107239 / 10 ^ 8 : ℝ) *
          (1 / b - 1 / ((a : ℝ) * Nat.sqrt a))) /
        (((178107239 / 10 ^ 8 : ℝ) *
          ((logLower a : ℝ) / scale + 2 / (Nat.sqrt a + 1 : ℕ))) *
          ((178107239 / 10 ^ 8 : ℝ) *
            ((logLower a : ℝ) / scale + 2 / (Nat.sqrt a + 1 : ℕ)) +
            ((178107239 / 10 ^ 8 : ℝ) *
              (1 / b - 1 / ((a : ℝ) * Nat.sqrt a))) * (b - a : ℕ))) := by
  rcases parameters_valid a b v hvalid with
    ⟨ha, hab, hbound, hv, hbar, hnum⟩
  let r := Nat.sqrt a
  let bn := 178107239 * (logLower a * (r + 1) + 2 * scale)
  let bd := 10 ^ 8 * scale * (r + 1)
  let cn := 178107239 * (a * r - b)
  let cd := 10 ^ 8 * b * a * r
  have hbn : 0 < bn := by
    dsimp [bn]
    have h2 : 0 < 2 * scale := Nat.mul_pos (by decide) scale_pos
    exact Nat.mul_pos (by decide) (by omega)
  have hbd : 0 < bd := by
    dsimp [bd]
    exact Nat.mul_pos (Nat.mul_pos (by norm_num) scale_pos) (by omega)
  have hr : 0 < r := by
    have := (sqrt_bracket a (by omega : 1 ≤ a)).1
    exact_mod_cast this
  have hcd : 0 < cd := by
    dsimp [cd]
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by norm_num)
      (by omega : 0 < b)) (by omega : 0 < a)) hr
  have hvalB : ((bn : ℝ) / bd) =
      (178107239 / 10 ^ 8 : ℝ) *
        ((logLower a : ℝ) / scale + 2 / (r + 1 : ℕ)) := by
    simpa only [bn, bd, Nat.cast_add, Nat.cast_one] using
      intercept_value scale a r (logLower a) scale_pos
  have hvalC : ((cn : ℝ) / cd) =
      (178107239 / 10 ^ 8 : ℝ) *
        (1 / b - 1 / ((a : ℝ) * r)) := by
    simpa only [cn, cd] using slope_value a b r
      (by omega) (by omega) hr hbar.le
  have hq : (1 : ℝ) / ((v : ℝ) / scale) = (scale : ℝ) / v := by
    have hv' : (0 : ℝ) < v := by exact_mod_cast hv
    have hD' : (0 : ℝ) < scale := by exact_mod_cast scale_pos
    field_simp
  have hs := slope_lower 16384 (a + 1) scale v bn bd cn cd (b - a)
    (by norm_num) hv hbn hbd hcd
  change ((parameters a b v).slope : ℝ) / 16384 ≤
    (a + 1 : ℝ) * (1 / ((v : ℝ) / scale)) *
      ((178107239 / 10 ^ 8 : ℝ) *
        (1 / b - 1 / ((a : ℝ) * r))) /
      (((178107239 / 10 ^ 8 : ℝ) *
        ((logLower a : ℝ) / scale + 2 / (r + 1 : ℕ))) *
        ((178107239 / 10 ^ 8 : ℝ) *
          ((logLower a : ℝ) / scale + 2 / (r + 1 : ℕ)) +
          ((178107239 / 10 ^ 8 : ℝ) *
            (1 / b - 1 / ((a : ℝ) * r))) * (b - a : ℕ)))
  rw [hq, ← hvalB, ← hvalC]
  simpa only [parameters, forceNat_eq, Nat.cast_add, Nat.cast_one,
    Nat.cast_ofNat, r, bn, bd, cn, cd] using hs

theorem parameterized_bound (a b v k : ℕ) (x : ℝ)
    (hvalid : (parameters a b v).valid = true)
    (hax : (a : ℝ) ≤ x) (hxb : x ≤ b)
    (hv : ((v : ℝ) / scale) ≤ RosserMomentBridge.reciprocalProduct a)
    (hcard : (Nat.primesLE ⌊x⌋₊ \ Nat.primesLE a).card ≤ k)
    (hcount : (k : ℝ) <
      ((parameters a b v).intercept : ℝ) / 16384 +
        ((parameters a b v).slope : ℝ) / 16384 * (x - a)) :
    RosserBlockCheck.Bound x := by
  rcases parameters_valid a b v hvalid with
    ⟨ha, hab, hbmax, hv0, hbar, hnum⟩
  let r := Nat.sqrt a
  let g : ℝ := 178107239 / 10 ^ 8
  let L : ℝ := (logLower a : ℝ) / scale
  let S : ℝ := (r + 1 : ℕ)
  let B : ℝ := g * (L + 2 / S)
  let C : ℝ := g * (1 / b - 1 / ((a : ℝ) * r))
  let q : ℝ := (v : ℝ) / scale
  have hg : 0 ≤ g := by dsimp [g]; norm_num
  have hgamma : g ≤ Real.exp Real.eulerMascheroniConstant :=
    RosserProductCertificate.exp_gamma_lower
  have hsqrt := sqrt_bracket a (by omega : 1 ≤ a)
  have hr : 0 < (r : ℝ) := hsqrt.1
  have hrS : (r : ℝ) ≤ Real.sqrt a := hsqrt.2.1
  have hS : 0 < S := by dsimp [S]; positivity
  have hSa : Real.sqrt a ≤ S := hsqrt.2.2
  have hL : L ≤ Real.log a :=
    logLower_sound a (by omega : 1 ≤ a)
  have hB : 0 < B := by
    have hgp : 0 < g := by dsimp [g]; norm_num
    have hD : (0 : ℝ) < scale := by exact_mod_cast scale_pos
    have hL0 : 0 ≤ L :=
      div_nonneg (by exact_mod_cast Nat.zero_le (logLower a))
        (by exact_mod_cast Nat.zero_le scale)
    have h2 : 0 < 2 / S := by positivity
    exact mul_pos hgp (by linarith only [hL0, h2])
  have hC : 0 ≤ C := by
    have hval := slope_value a b r (by omega) (by omega)
      (by exact_mod_cast hr) hbar.le
    have hnonneg : (0 : ℝ) ≤
        ((178107239 * (a * r - b) : ℕ) : ℝ) /
          (10 ^ 8 * b * a * r : ℕ) := by positivity
    dsimp [C, g, r]
    rw [hval] at hnonneg
    exact hnonneg
  have hq : 0 < q := by
    dsimp [q]
    have hD : (0 : ℝ) < scale := by exact_mod_cast scale_pos
    have hv' : (0 : ℝ) < v := by exact_mod_cast hv0
    positivity
  have hI : ((parameters a b v).intercept : ℝ) / 16384 ≤
      (a + 1 : ℝ) * (1 - (1 / q) / B) :=
    parameters_intercept_lower a b v hvalid
  have hM : ((parameters a b v).slope : ℝ) / 16384 ≤
      (a + 1 : ℝ) * (1 / q) * C / (B * (B + C * (b - a : ℕ))) :=
    parameters_slope_lower a b v hvalid
  have hfloor : a ≤ ⌊x⌋₊ := Nat.le_floor hax
  have hrealha : (2 : ℝ) ≤ a := by exact_mod_cast (show 2 ≤ a by omega)
  have hd : 0 ≤ x - a := sub_nonneg.mpr hax
  have hdh : x - (a : ℝ) ≤ (b - a : ℕ) := by
    rw [Nat.cast_sub hab.le]
    linarith only [hxb]
  have hp := RosserPrefixBounds.affine_prefix_to_product a ⌊x⌋₊ k q B C
    (b - a : ℕ) (x - a)
    (((parameters a b v).intercept : ℝ) / 16384)
    (((parameters a b v).slope : ℝ) / 16384)
    (by omega) hfloor hq hB hC hd hdh hv hcard hI hM hcount
  have ht := RosserPrefixBounds.rounded_target_linear_lower
    (a : ℝ) b x g L r S (by linarith only [hrealha]) hax hxb hg hgamma
    hL hr hrS hS hSa
  change RosserProductCertificate.eulerProduct ⌊x⌋₊ <
    Real.exp Real.eulerMascheroniConstant * Real.log x +
      2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x
  calc
    RosserProductCertificate.eulerProduct ⌊x⌋₊ < B + C * (x - a) := hp
    _ ≤ Real.exp Real.eulerMascheroniConstant *
        (Real.log x + 2 / Real.sqrt x) := ht
    _ = _ := by ring

end RosserPrefixParams

-- Source: Solutions/RosserBitSieve.lean
/-!
A bit sieve using only natural-number arithmetic, suitable for kernel reduction.
The divisors are untrusted data: they need only satisfy 2 <= d < a.
No claim that the divisor list is complete or consists of primes is required.
-/

namespace RosserBitSieve

theorem periodicMask_eq_sum (d count : ℕ) (hd : 0 < d) :
    periodicMask d count = ∑ i ∈ Finset.range count, (2 ^ d) ^ i := by
  rw [Nat.geomSum_eq (Nat.one_lt_two_pow (Nat.ne_of_gt hd)), periodicMask, pow_mul]

theorem periodicMask_succ (d count : ℕ) (hd : 0 < d) :
    periodicMask d (count + 1) = 2 ^ d * periodicMask d count + 1 := by
  rw [periodicMask_eq_sum d (count + 1) hd, periodicMask_eq_sum d count hd,
    geom_sum_succ]

/-- Every set bit in a periodic mask has index divisible by d. -/
theorem periodicMask_bit_dvd (d count i : ℕ) (hd : 0 < d)
    (hbit : (periodicMask d count).testBit i = true) : d ∣ i := by
  induction count generalizing i with
  | zero => simp [periodicMask] at hbit
  | succ count ih =>
    rw [periodicMask_succ d count hd,
      Nat.testBit_two_pow_mul_add _ (Nat.one_lt_two_pow (Nat.ne_of_gt hd))] at hbit
    split at hbit
    · have hone : (1 : ℕ).testBit i = decide (i = 0) := by
        simpa only [Nat.pow_zero, eq_comm] using (Nat.testBit_two_pow (n := 0) (m := i))
      rw [hone] at hbit
      have hi : i = 0 := of_decide_eq_true hbit
      subst i
      exact dvd_zero d
    · rename_i hi
      have hdiv := ih (i - d) hbit
      have heq : i = (i - d) + d := by omega
      rw [heq]
      exact dvd_add hdiv (dvd_refl d)

theorem first_multiple (a d : ℕ) (hd : 0 < d) :
    d ∣ a + (d - a % d) % d := by
  apply Nat.dvd_of_mod_eq_zero
  by_cases hz : a % d = 0
  · simp [hz]
  · have hm := Nat.mod_lt a hd
    have hsmall : d - a % d < d := by omega
    rw [Nat.mod_eq_of_lt hsmall, Nat.add_mod]
    rw [Nat.mod_eq_of_lt hsmall, Nat.add_sub_of_le hm.le, Nat.mod_self]

theorem divisorMask_bit_dvd (a len d i : ℕ) (hd : 0 < d)
    (hbit : (divisorMask a len d).testBit i = true) : d ∣ a + i := by
  unfold divisorMask at hbit
  rw [Nat.testBit_mul_two_pow, Bool.and_eq_true] at hbit
  obtain ⟨hoffset, hperiodic⟩ := hbit
  have hoffset' : (d - a % d) % d ≤ i := of_decide_eq_true hoffset
  have hp := periodicMask_bit_dvd d _ _ hd hperiodic
  have hfirst := first_multiple a d hd
  have heq : a + i = (a + (d - a % d) % d) + (i - (d - a % d) % d) := by omega
  rw [heq]
  exact dvd_add hfirst hp

theorem divisorMask_preserves_prime (a len d i : ℕ)
    (hd : 2 ≤ d) (hda : d < a) (hp : Nat.Prime (a + i)) :
    (divisorMask a len d).testBit i = false := by
  apply Bool.eq_false_iff.mpr
  intro hbit
  have hdiv := divisorMask_bit_dvd a len d i (by omega) hbit
  rcases hp.eq_one_or_self_of_dvd d hdiv with h | h <;> omega

theorem compositeMask_preserves_prime (divisors : List ℕ) (a len i : ℕ)
    (hds : ∀ d ∈ divisors, 2 ≤ d ∧ d < a) (hp : Nat.Prime (a + i)) :
    (compositeMask divisors a len).testBit i = false := by
  suffices h : ∀ mask : ℕ, mask.testBit i = false →
      (divisors.foldl (fun mask d => mask ||| divisorMask a len d) mask).testBit i = false by
    exact h 0 (by simp)
  induction divisors with
  | nil => simp
  | cons d ds ih =>
    intro mask hmask
    apply ih (fun q hq => hds q (by simp [hq]))
    rw [Nat.testBit_or, hmask, divisorMask_preserves_prime a len d i
      (hds d (by simp)).1 (hds d (by simp)).2 hp]
    rfl

theorem candidateMask_preserves_prime (divisors : List ℕ) (a len i : ℕ)
    (hds : ∀ d ∈ divisors, 2 ≤ d ∧ d < a) (hi : i < len)
    (hp : Nat.Prime (a + i)) :
    (candidateMask divisors a len).testBit i = true := by
  simp [candidateMask, Nat.testBit_xor, Nat.testBit_two_pow_sub_one,
    Nat.testBit_mod_two_pow, hi, compositeMask_preserves_prime divisors a len i hds hp]

theorem mem_enumBits (depth start mask x : ℕ) :
    x ∈ enumBits depth start mask ↔
      start ≤ x ∧ x < start + 2 ^ depth ∧ mask.testBit (x - start) = true := by
  induction depth generalizing start mask with
  | zero =>
    simp only [enumBits, Nat.pow_zero]
    split
    · rename_i h
      have hm : mask % 2 = 1 := by simpa using h
      constructor
      · intro hx
        have hx' : x = start := by simpa using hx
        subst x
        simp [Nat.testBit_eq_decide_div_mod_eq, hm]
      · intro hx
        have hx' : x = start := by omega
        simp [hx']
    · rename_i h
      have hm : mask % 2 ≠ 1 := by simpa using h
      constructor
      · simp
      · intro hx
        have hx' : x = start := by omega
        subst x
        simp [Nat.testBit_eq_decide_div_mod_eq, hm] at hx
  | succ depth ih =>
    by_cases hm : mask = 0
    · subst mask
      simp [enumBits]
    · simp only [enumBits, beq_iff_eq, hm, if_false, List.mem_append, ih,
        Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Bool.and_eq_true,
        decide_eq_true_eq, Nat.pow_succ]
      constructor
      · intro hx
        rcases hx with ⟨hlo, hhi, _, hb⟩ | ⟨hlo, hhi, hb⟩
        · exact ⟨hlo, by omega, hb⟩
        · refine ⟨by omega, by omega, ?_⟩
          have heq : x - (start + 2 ^ depth) + 2 ^ depth = x - start := by omega
          simpa only [heq] using hb
      · intro ⟨hlo, hhi, hb⟩
        by_cases hleft : x < start + 2 ^ depth
        · exact Or.inl ⟨hlo, hleft, by omega, hb⟩
        · right
          refine ⟨by omega, by omega, ?_⟩
          have heq : x - (start + 2 ^ depth) + 2 ^ depth = x - start := by omega
          simpa only [heq] using hb

theorem enumBits_nodup (depth start mask : ℕ) : (enumBits depth start mask).Nodup := by
  induction depth generalizing start mask with
  | zero => simp only [enumBits]; split <;> simp
  | succ depth ih =>
    simp only [enumBits]
    split
    · simp
    · apply List.Nodup.append (ih _ _) (ih _ _)
      apply List.disjoint_left.mpr
      intro x hx hx'
      have hleft := (mem_enumBits _ _ _ _).mp hx
      have hright := (mem_enumBits _ _ _ _).mp hx'
      omega

theorem candidateMask_bit (divisors : List ℕ) (a len i : ℕ) :
    (candidateMask divisors a len).testBit i =
      (decide (i < len) && !(compositeMask divisors a len).testBit i) := by
  by_cases hi : i < len <;>
    simp [candidateMask, Nat.testBit_xor, Nat.testBit_two_pow_sub_one,
      Nat.testBit_mod_two_pow, hi]

theorem offsets_lt (divisors : List ℕ) (depth a len i : ℕ)
    (hi : i ∈ offsets divisors depth a len) : i < len := by
  have hb := (mem_enumBits _ _ _ _).mp hi
  simp only [Nat.sub_zero, candidateMask_bit, Bool.and_eq_true, decide_eq_true_eq] at hb
  exact hb.2.2.1

theorem offsets_preserve_primes (divisors : List ℕ) (depth a len p : ℕ)
    (hds : ∀ d ∈ divisors, 2 ≤ d ∧ d < a) (hlen : len ≤ 2 ^ depth)
    (hpa : a ≤ p) (hpB : p < a + len) (hp : Nat.Prime p) :
    p - a ∈ offsets divisors depth a len := by
  apply (mem_enumBits _ _ _ _).mpr
  refine ⟨Nat.zero_le _, by omega, ?_⟩
  simp only [Nat.sub_zero]
  apply candidateMask_preserves_prime divisors a len (p - a) hds (by omega)
  simpa only [Nat.add_sub_of_le hpa] using hp

theorem offsets_nodup (divisors : List ℕ) (depth a len : ℕ) :
    (offsets divisors depth a len).Nodup := enumBits_nodup _ _ _

theorem mem_windowOffsets (depth mask shift len d : ℕ) :
    d ∈ windowOffsets depth mask shift len ↔
      0 < d ∧ d ≤ len ∧ d ≤ 2 ^ depth ∧ mask.testBit (d - 1 + shift) = true := by
  simp only [windowOffsets, List.mem_map, mem_enumBits, Nat.zero_add, Nat.sub_zero,
    Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Bool.and_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨i, ⟨_, hi, hlen, hb⟩, rfl⟩
    exact ⟨by omega, by omega, by omega, by simpa using hb⟩
  · rintro ⟨hd, hlen, hdepth, hb⟩
    exact ⟨d - 1, ⟨Nat.zero_le _, by omega, by omega, hb⟩, by omega⟩

theorem windowOffsets_nodup (depth mask shift len : ℕ) :
    (windowOffsets depth mask shift len).Nodup := by
  apply List.Nodup.map _ (enumBits_nodup _ _ _)
  intro a b h
  change a + 1 = b + 1 at h
  omega

end RosserBitSieve

-- Source: Solutions/RosserPackedBarrier.lean
/-! Arithmetic lemmas for the packed prefix-count certificate. -/

namespace RosserPackedBarrier

theorem forceNat_eq {α : Sort _} (n : ℕ) (f : ℕ → α) :
    RosserScan.forceNat n f = f n := by
  cases n <;> rfl

def candidateCount (mask d : ℕ) : ℕ :=
  ((List.range d).filter (fun i => mask.testBit i)).length

/-- Little-endian packing with a fixed number of digits. -/
def pack (q : ℕ) : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, f => f 0 + q * pack q n (fun i => f (i + 1))

theorem pack_congr (q n : ℕ) {f g : ℕ → ℕ}
    (h : ∀ i < n, f i = g i) : pack q n f = pack q n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [pack]
    rw [h 0 (by omega), ih (fun i hi => h (i + 1) (by omega))]

theorem pack_add (q n : ℕ) (f g : ℕ → ℕ) :
    pack q n (fun i => f i + g i) = pack q n f + pack q n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih => simp only [pack, ih]; ring

theorem pack_mul (q n c : ℕ) (f : ℕ → ℕ) :
    pack q n (fun i => c * f i) = c * pack q n f := by
  induction n generalizing f with
  | zero => simp [pack]
  | succ n ih => simp only [pack, ih]; ring

theorem pack_mono (q n : ℕ) {f g : ℕ → ℕ}
    (h : ∀ i < n, f i ≤ g i) : pack q n f ≤ pack q n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    exact Nat.add_le_add (h 0 (by omega))
      (Nat.mul_le_mul_left q (ih (fun i hi => h (i + 1) (by omega))))

theorem pack_sub (q n : ℕ) {f g : ℕ → ℕ}
    (h : ∀ i < n, g i ≤ f i) :
    pack q n (fun i => f i - g i) = pack q n f - pack q n g := by
  have heq : pack q n (fun i => f i - g i) + pack q n g = pack q n f := by
    rw [← pack_add]
    exact pack_congr q n (fun i hi => Nat.sub_add_cancel (h i hi))
  omega

theorem pack_lt (q n : ℕ) (hq : 0 < q) {f : ℕ → ℕ}
    (h : ∀ i < n, f i < q) : pack q n f < q ^ n := by
  induction n generalizing f with
  | zero => simp [pack]
  | succ n ih =>
    have htail := ih (fun i hi => h (i + 1) (by omega))
    have hhead := h 0 (by omega)
    simp only [pack, pow_succ]
    nlinarith

theorem pack_mod (q n : ℕ) (hq : 0 < q) {f : ℕ → ℕ}
    (h : f 0 < q) : pack q (n + 1) f % q = f 0 := by
  simp [pack, Nat.mod_eq_of_lt h]

theorem pack_div (q n : ℕ) (hq : 0 < q) {f : ℕ → ℕ}
    (h : f 0 < q) : pack q (n + 1) f / q = pack q n (fun i => f (i + 1)) := by
  simp [pack, Nat.add_mul_div_left _ _ hq, Nat.div_eq_of_lt h]

theorem pack_digit (q n i : ℕ) (hq : 0 < q) {f : ℕ → ℕ}
    (h : ∀ j < n, f j < q) (hi : i < n) :
    pack q n f / q ^ i % q = f i := by
  induction i generalizing n f with
  | zero =>
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simpa using pack_mod q n hq (h 0 (by omega))
  | succ i ih =>
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [pow_succ', ← Nat.div_div_eq_div_mul, pack_div q n hq (h 0 (by omega))]
    exact ih n (fun j hj => h (j + 1) (by omega)) (by omega)

theorem pack_eq_sum (q n : ℕ) (f : ℕ → ℕ) :
    pack q n f = ∑ i ∈ Finset.range n, f i * q ^ i := by
  induction n generalizing f with
  | zero => simp [pack]
  | succ n ih =>
    rw [pack, ih, Finset.sum_range_succ']
    simp only [pow_zero, Nat.mul_one, Finset.mul_sum, pow_succ]
    rw [Nat.add_comm (f 0)]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring

theorem pack_const_one (q n : ℕ) (hq : 1 < q) :
    pack q n (fun _ => 1) = (q ^ n - 1) / (q - 1) := by
  rw [pack_eq_sum]
  simp only [Nat.one_mul]
  exact Nat.geomSum_eq hq n

theorem pack_const (q n c : ℕ) :
    pack q n (fun _ => c) = c * pack q n (fun _ => 1) := by
  simpa using pack_mul q n c (fun _ => 1)

theorem pack_one_identity (q n : ℕ) (hq : 1 ≤ q) :
    (q - 1) * pack q n (fun _ => 1) + 1 = q ^ n := by
  induction n with
  | zero => simp [pack]
  | succ n ih =>
    simp only [pack, pow_succ]
    have hq' := Nat.sub_add_cancel hq
    nlinarith

def prefixSum (f : ℕ → ℕ) (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, f i

@[simp] theorem prefixSum_one (f : ℕ → ℕ) : prefixSum f 1 = f 0 := by
  simp [prefixSum]

theorem prefixSum_shift (f : ℕ → ℕ) (n : ℕ) :
    prefixSum f (n + 1) = f 0 + prefixSum (fun i => f (i + 1)) n := by
  simp [prefixSum, Finset.sum_range_succ', Nat.add_comm]

theorem pack_prefix_identity (q n : ℕ) (f : ℕ → ℕ) (hq : 1 ≤ q) :
    (q - 1) * pack q n (fun i => prefixSum f (i + 1)) + pack q n f =
      q ^ n * prefixSum f n := by
  induction n generalizing f with
  | zero => simp [pack, prefixSum]
  | succ n ih =>
    have hy : pack q (n + 1) (fun i => prefixSum f (i + 1)) =
        f 0 + q * (f 0 * pack q n (fun _ => 1) +
          pack q n (fun i => prefixSum (fun j => f (j + 1)) (i + 1))) := by
      rw [pack, prefixSum_one, ← pack_const, ← pack_add]
      congr 2
      apply pack_congr
      intro i hi
      exact prefixSum_shift f (i + 1)
    rw [hy, pack, prefixSum_shift, pow_succ]
    have htail := congrArg (fun x => q * x) (ih (fun i => f (i + 1)))
    have hr := congrArg (fun x => q * f 0 * x) (pack_one_identity q n hq)
    have hq' := Nat.sub_add_cancel hq
    nlinarith

theorem prefixSum_mono (f : ℕ → ℕ) {a b : ℕ} (h : a ≤ b) :
    prefixSum f a ≤ prefixSum f b := by
  exact Finset.sum_le_sum_of_subset (Finset.range_mono h)

/-- Multiplication by a repunit packs all cumulative digit sums at once. -/
theorem pack_prefix_mod (q n : ℕ) (f : ℕ → ℕ) (hq : 1 < q)
    (hsum : prefixSum f n < q) :
    (pack q n f * pack q n (fun _ => 1)) % q ^ n =
      pack q n (fun i => prefixSum f (i + 1)) := by
  have hcop : Nat.Coprime (q ^ n) (q - 1) := by
    apply Nat.Coprime.pow_left
    exact (Nat.coprime_self_sub_right (by omega : 1 ≤ q)).mpr (by simp)
  have hx : (q - 1) * (pack q n f * pack q n (fun _ => 1)) + pack q n f =
      q ^ n * pack q n f := by
    have := congrArg (fun x => pack q n f * x) (pack_one_identity q n (by omega))
    nlinarith
  have heq :
      (q - 1) * (pack q n f * pack q n (fun _ => 1)) + pack q n f ≡
      (q - 1) * pack q n (fun i => prefixSum f (i + 1)) + pack q n f [MOD q ^ n] := by
    rw [hx, pack_prefix_identity q n f (by omega)]
    simp [Nat.ModEq]
  have heq' := Nat.ModEq.add_right_cancel (Nat.ModEq.refl (pack q n f)) heq
  have hc := Nat.ModEq.cancel_left_of_coprime hcop heq'
  rw [Nat.ModEq, Nat.mod_eq_of_lt (pack_lt q n (by omega) (fun i hi =>
    (prefixSum_mono f (by omega : i + 1 ≤ n)).trans_lt hsum))] at hc
  exact hc

theorem pack_testBit (w n i j : ℕ) {f : ℕ → ℕ}
    (h : ∀ k < n, f k < 2 ^ w) (hi : i < n) (hj : j < w) :
    (pack (2 ^ w) n f).testBit (w * i + j) = (f i).testBit j := by
  have hd := pack_digit (2 ^ w) n i (by positivity) h hi
  have hb := congrArg (fun x : ℕ => x.testBit j) hd
  rw [Nat.testBit_mod_two_pow, show decide (j < w) = true by simp [hj],
    Bool.true_and] at hb
  simpa only [← pow_mul, Nat.testBit_div_two_pow, Nat.add_comm] using hb

theorem pack_testBit_all (w n k : ℕ) (hw : 0 < w) {f : ℕ → ℕ}
    (h : ∀ i < n, f i < 2 ^ w) :
    (pack (2 ^ w) n f).testBit k =
      if k / w < n then (f (k / w)).testBit (k % w) else false := by
  have hdecomp := Nat.mod_add_div k w
  by_cases hi : k / w < n
  · rw [if_pos hi]
    have hk : k = w * (k / w) + k % w := by omega
    simpa only [← hk] using pack_testBit w n (k / w) (k % w) h hi (Nat.mod_lt k hw)
  · rw [if_neg hi]
    have hkn : w * n ≤ k := by
      have := Nat.mul_le_mul_left w (by omega : n ≤ k / w)
      omega
    apply Nat.testBit_eq_false_of_lt
    apply (pack_lt (2 ^ w) n (by positivity) h).trans_le
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by omega) hkn

theorem pack_and (w n : ℕ) (hw : 0 < w) (f g : ℕ → ℕ)
    (hf : ∀ i < n, f i < 2 ^ w) (hg : ∀ i < n, g i < 2 ^ w) :
    pack (2 ^ w) n f &&& pack (2 ^ w) n g =
      pack (2 ^ w) n (fun i => f i &&& g i) := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_and, pack_testBit_all w n k hw hf, pack_testBit_all w n k hw hg,
    pack_testBit_all w n k hw (fun i hi => Nat.and_le_left.trans_lt (hf i hi))]
  split_ifs <;> simp [Nat.testBit_and]

/-- A low mask discards exactly the bits shifted in from the next digit. -/
theorem pack_shift_and (w n s : ℕ) (hw : 0 < w) (hs : s ≤ w) (f g : ℕ → ℕ)
    (hf : ∀ i < n, f i < 2 ^ w) (hg : ∀ i < n, g i < 2 ^ (w - s)) :
    (pack (2 ^ w) n f >>> s) &&& pack (2 ^ w) n g =
      pack (2 ^ w) n (fun i => (f i >>> s) &&& g i) := by
  have hg' : ∀ i < n, g i < 2 ^ w := fun i hi =>
    (hg i hi).trans_le (Nat.pow_le_pow_right (by omega) (by omega))
  have hout : ∀ i < n, ((f i >>> s) &&& g i) < 2 ^ w := fun i hi =>
    Nat.and_le_right.trans_lt (hg' i hi)
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_and, pack_testBit_all w n k hw hg', pack_testBit_all w n k hw hout]
  by_cases hi : k / w < n
  · rw [if_pos hi, if_pos hi, Nat.testBit_and]
    by_cases hb : (g (k / w)).testBit (k % w) = true
    · have hsmall : k % w < w - s := by
        by_contra hh
        have hfals := Nat.testBit_eq_false_of_lt ((hg (k / w) hi).trans_le
          (Nat.pow_le_pow_right (by omega) (by omega : w - s ≤ k % w)))
        simp [hb] at hfals
      have hd := Nat.mod_add_div k w
      have heq : s + k = w * (k / w) + (k % w + s) := by omega
      rw [Nat.testBit_shiftRight, heq, pack_testBit w n (k / w) (k % w + s) hf hi
        (by omega), Nat.testBit_shiftRight]
      simp [Nat.add_comm]
    · simp [Bool.eq_false_iff.mpr hb]
  · simp [hi]

theorem pack_pair (q n : ℕ) (f : ℕ → ℕ) :
    pack q (2 * n) f = pack (q * q) n (fun i => f (2 * i) + q * f (2 * i + 1)) := by
  induction n generalizing f with
  | zero => simp [pack]
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
    simp only [pack]
    rw [ih]
    have heq :
        pack (q * q) n (fun i => f (2 * i + 1 + 1) + q * f (2 * i + 1 + 1 + 1)) =
        pack (q * q) n (fun i => f (2 * (i + 1)) + q * f (2 * (i + 1) + 1)) := by
      apply pack_congr
      intro i hi
      congr 2 <;> omega
    rw [heq]
    ring

theorem pack_digits (w n mask : ℕ) (hw : 0 < w) (hm : mask < 2 ^ (w * n)) :
    pack (2 ^ w) n (fun i => mask / 2 ^ (w * i) % 2 ^ w) = mask := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [pack_testBit_all w n k hw (fun i hi => Nat.mod_lt _ (by positivity))]
  by_cases hi : k / w < n
  · rw [if_pos hi, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
    have hj := Nat.mod_lt k hw
    simp only [show decide (k % w < w) = true by simp [hj], Bool.true_and]
    rw [Nat.mod_add_div]
  · rw [if_neg hi]
    symm
    apply Nat.testBit_eq_false_of_lt
    apply hm.trans_le (Nat.pow_le_pow_right (by omega) ?_)
    have hdecomp := Nat.mod_add_div k w
    have := Nat.mul_le_mul_left w (by omega : n ≤ k / w)
    omega

theorem stripe_eq (w n : ℕ) (hw : 0 < w) :
    (2 ^ (2 * w * n) - 1) / (2 ^ w + 1) =
      pack (2 ^ (2 * w)) n (fun _ => 2 ^ w - 1) := by
  have hq : 1 ≤ 2 ^ w := Nat.succ_le_of_lt (Nat.two_pow_pos w)
  have hr := pack_one_identity (2 ^ (2 * w)) n
    (Nat.succ_le_of_lt (Nat.two_pow_pos (2 * w)))
  have hpow : 2 ^ (2 * w) = 2 ^ w * 2 ^ w := by
    rw [two_mul, pow_add]
  have hsub : 2 ^ (2 * w) - 1 = (2 ^ w + 1) * (2 ^ w - 1) := by
    have := Nat.sub_add_cancel hq
    rw [hpow]
    have hs := Nat.sub_add_cancel (show 1 ≤ 2 ^ w * 2 ^ w by nlinarith)
    nlinarith
  have hall : 2 ^ (2 * w * n) - 1 =
      (2 ^ w + 1) * ((2 ^ w - 1) * pack (2 ^ (2 * w)) n (fun _ => 1)) := by
    rw [pow_mul, ← hr, Nat.add_sub_cancel, hsub]
    ring
  rw [hall, Nat.mul_div_cancel_left _ (by positivity)]
  exact (pack_const _ _ _).symm

/-- One parallel pairwise population-count step. -/
def mergeCounts (w n x : ℕ) : ℕ :=
  RosserScan.forceNat ((2 ^ (2 * w * n) - 1) / (2 ^ w + 1)) fun stripe =>
    (x &&& stripe) + ((x >>> w) &&& stripe)

theorem mergeCounts_sound (w n : ℕ) (hw : 0 < w) (f : ℕ → ℕ)
    (hf : ∀ i < 2 * n, f i < 2 ^ w) :
    mergeCounts w n (pack (2 ^ w) (2 * n) f) =
      pack (2 ^ (2 * w)) n (fun i => f (2 * i) + f (2 * i + 1)) := by
  have hq : 0 < 2 ^ w := by positivity
  have hpow : 2 ^ w * 2 ^ w = 2 ^ (2 * w) := by rw [two_mul, pow_add]
  let g := fun i => f (2 * i) + 2 ^ w * f (2 * i + 1)
  have hg : ∀ i < n, g i < 2 ^ (2 * w) := by
    intro i hi
    have h0 := hf (2 * i) (by omega)
    have h1 := hf (2 * i + 1) (by omega)
    dsimp [g]
    rw [← hpow]
    nlinarith
  have hm : ∀ i < n, 2 ^ w - 1 < 2 ^ (2 * w - w) := by
    intro i hi
    rw [show 2 * w - w = w by omega]
    omega
  have hlo : ∀ i < n, (g i &&& (2 ^ w - 1)) = f (2 * i) := by
    intro i hi
    simp only [g, Nat.and_two_pow_sub_one_eq_mod, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (hf (2 * i) (by omega))]
  have hhi : ∀ i < n, ((g i >>> w) &&& (2 ^ w - 1)) = f (2 * i + 1) := by
    intro i hi
    simp only [g, Nat.shiftRight_eq_div_pow, Nat.add_mul_div_left _ _ hq,
      Nat.div_eq_of_lt (hf (2 * i) (by omega)), Nat.zero_add,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (hf (2 * i + 1) (by omega))]
  simp only [mergeCounts, forceNat_eq, stripe_eq w n hw, pack_pair, hpow]
  change (pack (2 ^ (2 * w)) n g &&& pack (2 ^ (2 * w)) n (fun _ => 2 ^ w - 1)) +
    ((pack (2 ^ (2 * w)) n g >>> w) &&& pack (2 ^ (2 * w)) n (fun _ => 2 ^ w - 1)) = _
  rw [pack_and (2 * w) n (by omega) g _ hg (fun i hi => (hm i hi).trans_le
    (Nat.pow_le_pow_right (by omega) (by omega))),
    pack_shift_and (2 * w) n w (by omega) (by omega) g _ hg hm, ← pack_add]
  apply pack_congr
  intro i hi
  rw [hlo i hi, hhi i hi]

def bitValue (mask i : ℕ) : ℕ := (mask.testBit i).toNat

theorem bitValue_le_one (mask i : ℕ) : bitValue mask i ≤ 1 := by
  unfold bitValue
  cases mask.testBit i <;> decide

theorem bitValue_eq_digit (mask i : ℕ) : bitValue mask i = mask / 2 ^ i % 2 := by
  simp only [bitValue, Nat.testBit_eq_decide_div_mod_eq]
  have h := Nat.mod_lt (mask / 2 ^ i) (by omega : 0 < 2)
  by_cases heq : mask / 2 ^ i % 2 = 1
  · simp [heq]
  · have hz : mask / 2 ^ i % 2 = 0 := by omega
    simp [hz]

theorem candidateCount_eq_sum (mask d : ℕ) :
    candidateCount mask d = prefixSum (bitValue mask) d := by
  induction d with
  | zero => simp [candidateCount, prefixSum]
  | succ d ih =>
    simp only [candidateCount, List.range_succ, List.filter_append, List.length_append,
      prefixSum, Finset.sum_range_succ] at *
    rw [ih]
    cases h : mask.testBit d <;> simp [List.filter, bitValue, h]

def blockSum (f : ℕ → ℕ) (w j : ℕ) : ℕ :=
  ∑ i ∈ Finset.range w, f (w * j + i)

@[simp] theorem blockSum_one (f : ℕ → ℕ) (j : ℕ) : blockSum f 1 j = f j := by
  simp [blockSum]

theorem blockSum_le (f : ℕ → ℕ) (hf : ∀ i, f i ≤ 1) (w j : ℕ) :
    blockSum f w j ≤ w := by
  calc
    _ ≤ ∑ _i ∈ Finset.range w, 1 := Finset.sum_le_sum (fun i hi => hf _)
    _ = _ := by simp

theorem blockSum_pair (f : ℕ → ℕ) (w j : ℕ) :
    blockSum f (2 * w) j = blockSum f w (2 * j) + blockSum f w (2 * j + 1) := by
  unfold blockSum
  rw [show 2 * w = w + w by omega, Finset.sum_range_add]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> congr 1 <;> ring

theorem prefixSum_blocks (f : ℕ → ℕ) (w n : ℕ) :
    prefixSum (blockSum f w) n = prefixSum f (w * n) := by
  induction n with
  | zero => simp [prefixSum]
  | succ n ih =>
    change (∑ i ∈ Finset.range (n + 1), blockSum f w i) = _
    rw [Finset.sum_range_succ]
    change prefixSum (blockSum f w) n + blockSum f w n = _
    rw [ih, Nat.mul_add, Nat.mul_one]
    simp only [prefixSum, blockSum, Finset.sum_range_add]

theorem mergeCounts_blocks (w n : ℕ) (hw : 0 < w) (f : ℕ → ℕ)
    (hf : ∀ i, f i ≤ 1) :
    mergeCounts w n (pack (2 ^ w) (2 * n) (blockSum f w)) =
      pack (2 ^ (2 * w)) n (blockSum f (2 * w)) := by
  rw [mergeCounts_sound w n hw _ (fun i hi =>
    (blockSum_le f hf w i).trans_lt Nat.lt_two_pow_self)]
  apply pack_congr
  intro i hi
  exact (blockSum_pair f w i).symm

/-- Five pairwise merge stages give one population count per 32-bit digit. -/
def packedCounts32 (mask n : ℕ) : ℕ :=
  RosserScan.forceNat (mergeCounts 1 (16 * n) mask) fun x =>
  RosserScan.forceNat (mergeCounts 2 (8 * n) x) fun x =>
  RosserScan.forceNat (mergeCounts 4 (4 * n) x) fun x =>
  RosserScan.forceNat (mergeCounts 8 (2 * n) x) fun x =>
    mergeCounts 16 n x

theorem packedCounts32_sound (mask n : ℕ) (hm : mask < 2 ^ (32 * n)) :
    packedCounts32 mask n = pack (2 ^ 32) n (blockSum (bitValue mask) 32) := by
  have hzero : pack 2 (32 * n) (blockSum (bitValue mask) 1) = mask := by
    calc
      _ = pack 2 (32 * n) (fun i => mask / 2 ^ i % 2) := by
        apply pack_congr
        intro i hi
        rw [blockSum_one, bitValue_eq_digit]
      _ = mask := by
        simpa only [Nat.one_mul, pow_one] using
          pack_digits 1 (32 * n) mask (by omega) (by simpa using hm)
  have h1 := mergeCounts_blocks 1 (16 * n) (by omega) (bitValue mask) (bitValue_le_one mask)
  have h2 := mergeCounts_blocks 2 (8 * n) (by omega) (bitValue mask) (bitValue_le_one mask)
  have h4 := mergeCounts_blocks 4 (4 * n) (by omega) (bitValue mask) (bitValue_le_one mask)
  have h8 := mergeCounts_blocks 8 (2 * n) (by omega) (bitValue mask) (bitValue_le_one mask)
  have h16 := mergeCounts_blocks 16 n (by omega) (bitValue mask) (bitValue_le_one mask)
  norm_num only [← Nat.mul_assoc, Nat.reduceMul] at h1 h2 h4 h8 h16
  rw [hzero] at h1
  simp only [packedCounts32, forceNat_eq, h1, h2, h4, h8, h16]
  norm_num

/-- With half-width guards, subtraction is digitwise and every comparison is checked. -/
theorem guard_sound32 (n : ℕ) (f g : ℕ → ℕ)
    (hf : ∀ i < n, f i < 2 ^ 31) (hg : ∀ i < n, g i < 2 ^ 31)
    (hcheck :
      ((pack (2 ^ 32) n g + pack (2 ^ 32) n (fun _ => 2 ^ 31) -
        pack (2 ^ 32) n f) &&& pack (2 ^ 32) n (fun _ => 2 ^ 31)) =
          pack (2 ^ 32) n (fun _ => 2 ^ 31)) :
    ∀ i < n, f i ≤ g i := by
  have hsub :
      pack (2 ^ 32) n g + pack (2 ^ 32) n (fun _ => 2 ^ 31) - pack (2 ^ 32) n f =
        pack (2 ^ 32) n (fun i => g i + 2 ^ 31 - f i) := by
    rw [← pack_add, pack_sub]
    intro i hi
    have := hf i hi
    omega
  rw [hsub] at hcheck
  have hout : ∀ i < n, g i + 2 ^ 31 - f i < 2 ^ 32 := by
    intro i hi
    have := hg i hi
    omega
  intro i hi
  have hb := congrArg (fun x : ℕ => x.testBit (32 * i + 31)) hcheck
  rw [Nat.testBit_and, pack_testBit 32 n i 31 hout hi (by omega),
    pack_testBit 32 n i 31 (by intro j hj; norm_num) hi (by omega)] at hb
  have hguard : (2 ^ 31 : ℕ).testBit 31 = true := by decide
  simp only [hguard, Bool.and_true] at hb
  simp only [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq] at hb
  have := hout i hi
  omega

theorem pack_index_identity (q n : ℕ) (hq : 1 ≤ q) (hn : 0 < n) :
    (q - 1) * pack q n (fun i => i) + pack q n (fun _ => 1) =
      (n - 1) * q ^ n + 1 := by
  have hprefix := pack_prefix_identity q n (fun _ => 1) hq
  have heq : pack q n (fun i => prefixSum (fun _ => 1) (i + 1)) =
      pack q n (fun i => i) + pack q n (fun _ => 1) := by
    rw [← pack_add]
    apply pack_congr
    intro i hi
    simp [prefixSum]
  rw [heq] at hprefix
  simp [prefixSum] at hprefix
  have hr := pack_one_identity q n hq
  have hn' := Nat.sub_add_cancel (by omega : 1 ≤ n)
  have hn'' := congrArg (fun x => x * q ^ n) hn'
  nlinarith

theorem pack_index_eq (q n : ℕ) (hq : 1 < q) (hn : 0 < n) :
    pack q n (fun i => i) =
      ((n - 1) * q ^ n + 1 - pack q n (fun _ => 1)) / (q - 1) := by
  have h := pack_index_identity q n (by omega) hn
  have heq : (n - 1) * q ^ n + 1 - pack q n (fun _ => 1) =
      (q - 1) * pack q n (fun i => i) := by omega
  rw [heq, Nat.mul_div_cancel_left _ (by omega)]

def checkFromCounts (counts n intercept slope : ℕ) : Bool :=
  RosserScan.forceNat (32 * n) fun L =>
  RosserScan.forceNat ((2 ^ L - 1) / (2 ^ 32 - 1)) fun R =>
  RosserScan.forceNat ((((counts <<< L) - counts) / (2 ^ 32 - 1)) % 2 ^ L) fun pref =>
  RosserScan.forceNat (32 * (((n - 1) * 2 ^ L + 1 - R) / (2 ^ 32 - 1))) fun pos =>
  RosserScan.forceNat (16384 * pref) fun lhs =>
  RosserScan.forceNat (intercept * R + slope * pos) fun rhs =>
  RosserScan.forceNat (2 ^ 31 * R) fun guard =>
    decide (((rhs + guard - lhs) &&& guard) = guard)

theorem packed_prefix_formula (n : ℕ) (f : ℕ → ℕ)
    (hsum : prefixSum f n < 2 ^ 32) :
    ((((pack (2 ^ 32) n f <<< (32 * n)) - pack (2 ^ 32) n f) /
      (2 ^ 32 - 1)) % 2 ^ (32 * n)) =
      pack (2 ^ 32) n (fun i => prefixSum f (i + 1)) := by
  have hr := pack_one_identity (2 ^ 32) n (by norm_num)
  have hp : 2 ^ (32 * n) - 1 =
      (2 ^ 32 - 1) * pack (2 ^ 32) n (fun _ => 1) := by
    rw [pow_mul]
    omega
  rw [Nat.shiftLeft_eq]
  have hnum : pack (2 ^ 32) n f * 2 ^ (32 * n) - pack (2 ^ 32) n f =
      (pack (2 ^ 32) n f * pack (2 ^ 32) n (fun _ => 1)) * (2 ^ 32 - 1) := by
    calc
      _ = pack (2 ^ 32) n f * (2 ^ (32 * n) - 1) := by
        rw [Nat.mul_sub_left_distrib, Nat.mul_one]
      _ = _ := by rw [hp]; ring
  rw [hnum, Nat.mul_div_cancel _ (by norm_num), pow_mul]
  exact pack_prefix_mod (2 ^ 32) n f (by norm_num) hsum

/-- The prefix/guard stage, with a semantic specification for its packed count input. -/
theorem checkFromCounts_sound (n intercept slope : ℕ) (f : ℕ → ℕ)
    (hn : 0 < n) (hcount : 16384 * prefixSum f n < 2 ^ 31)
    (hrhs : intercept + slope * (32 * (n - 1)) < 2 ^ 31)
    (hcheck : checkFromCounts (pack (2 ^ 32) n f) n intercept slope = true) :
    ∀ i < n, 16384 * prefixSum f (i + 1) ≤ intercept + slope * (32 * i) := by
  have hsum : prefixSum f n < 2 ^ 32 := by omega
  have hR : (2 ^ (32 * n) - 1) / (2 ^ 32 - 1) =
      pack (2 ^ 32) n (fun _ => 1) := by
    rw [pack_const_one _ _ (by norm_num), pow_mul]
  have hpos : ((n - 1) * 2 ^ (32 * n) + 1 - pack (2 ^ 32) n (fun _ => 1)) /
      (2 ^ 32 - 1) = pack (2 ^ 32) n (fun i => i) := by
    rw [pack_index_eq _ _ (by norm_num) hn, pow_mul]
  simp only [checkFromCounts, forceNat_eq, decide_eq_true_eq] at hcheck
  rw [hR, packed_prefix_formula n f hsum, hpos] at hcheck
  have hguard := guard_sound32 n
    (fun i => 16384 * prefixSum f (i + 1))
    (fun i => intercept + slope * (32 * i))
  apply hguard
  · intro i hi
    exact (Nat.mul_le_mul_left _ (prefixSum_mono f (by omega))).trans_lt hcount
  · intro i hi
    exact (Nat.add_le_add_left (Nat.mul_le_mul_left slope
      (Nat.mul_le_mul_left 32 (by omega : i ≤ n - 1))) intercept).trans_lt hrhs
  · simp only [pack_add, pack_mul, pack_const (2 ^ 32) n intercept,
      pack_const (2 ^ 32) n (2 ^ 31)]
    rw [show pack (2 ^ 32) n (HMul.hMul 32) =
      32 * pack (2 ^ 32) n (fun i => i) from pack_mul (2 ^ 32) n 32 (fun i => i)]
    exact hcheck

theorem candidateCount_mono (mask : ℕ) {a b : ℕ} (h : a ≤ b) :
    candidateCount mask a ≤ candidateCount mask b := by
  rw [candidateCount_eq_sum, candidateCount_eq_sum]
  exact prefixSum_mono _ h

theorem bitValue_eq_zero (mask len i : ℕ) (hm : mask < 2 ^ len) (hi : len ≤ i) :
    bitValue mask i = 0 := by
  have hb := Nat.testBit_eq_false_of_lt
    (hm.trans_le (Nat.pow_le_pow_right (by omega) hi))
  simp [bitValue, hb]

theorem candidateCount_pad (mask len top : ℕ) (hm : mask < 2 ^ len) (hl : len ≤ top) :
    candidateCount mask top = candidateCount mask len := by
  rw [candidateCount_eq_sum, candidateCount_eq_sum]
  have ht : top = len + (top - len) := by omega
  rw [ht]
  simp only [prefixSum, Finset.sum_range_add]
  have hz : ∑ i ∈ Finset.range (top - len), bitValue mask (len + i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact bitValue_eq_zero mask len (len + i) hm (by omega)
  rw [hz, Nat.add_zero]

def packedCheck (mask len intercept slope : ℕ) : Bool :=
  RosserScan.forceNat ((len + 31) / 32) fun n =>
  RosserScan.forceNat (packedCounts32 mask n) fun counts =>
    checkFromCounts counts n intercept slope

/-- A successful packed test bounds every candidate prefix, including a partial final bucket. -/
theorem packedCheck_sound (mask len intercept slope : ℕ)
    (hlen : 0 < len) (hm : mask < 2 ^ len)
    (hcount : 16384 * candidateCount mask len < 2 ^ 31)
    (hrhs : intercept + slope * (32 * ((len + 31) / 32 - 1)) < 2 ^ 31)
    (hcheck : packedCheck mask len intercept slope = true) :
    ∀ d ≤ len, 16384 * candidateCount mask d ≤
      intercept + slope * 32 * ((d - 1) / 32) := by
  let n := (len + 31) / 32
  have hn : 0 < n := by dsimp [n]; omega
  have hl : len ≤ 32 * n := by dsimp [n]; omega
  have hm32 : mask < 2 ^ (32 * n) :=
    hm.trans_le (Nat.pow_le_pow_right (by omega) hl)
  have hsum : prefixSum (blockSum (bitValue mask) 32) n = candidateCount mask len := by
    rw [prefixSum_blocks, ← candidateCount_eq_sum, candidateCount_pad mask len _ hm hl]
  have hc : checkFromCounts (pack (2 ^ 32) n (blockSum (bitValue mask) 32))
      n intercept slope = true := by
    simp only [packedCheck, forceNat_eq] at hcheck
    change checkFromCounts (packedCounts32 mask n) n intercept slope = true at hcheck
    rw [packedCounts32_sound mask n hm32] at hcheck
    exact hcheck
  have hbound := checkFromCounts_sound n intercept slope (blockSum (bitValue mask) 32)
    hn (by simpa only [hsum] using hcount) hrhs hc
  intro d hd
  by_cases hz : d = 0
  · subst d
    simp [candidateCount]
  · have hi : (d - 1) / 32 < n := by dsimp [n]; omega
    have hend : d ≤ 32 * ((d - 1) / 32 + 1) := by omega
    have hb := hbound ((d - 1) / 32) hi
    rw [prefixSum_blocks, ← candidateCount_eq_sum] at hb
    exact (Nat.mul_le_mul_left 16384 (candidateCount_mono mask hend)).trans
      (by simpa only [Nat.mul_assoc] using hb)

end RosserPackedBarrier

-- Source: Solutions/RosserBitMoments.lean
/-! Compute the three moments of a bit window by bytes. A single packed
256-entry lookup table replaces eight recursive bit inspections. Its entire
contents are certified by `decide +kernel`; no native computation is trusted. -/

namespace RosserBitMoments

open RosserBitSieve AlternativeProductMoments

theorem moments_append (xs ys : List ℕ) :
    moments (xs ++ ys) = merge (moments xs) (moments ys) := by
  simp [moments, merge, List.map_append, List.sum_append]

theorem moments_shift (ds : List ℕ) (offset : ℕ) :
    moments (ds.map (fun d => offset + d)) = translate offset (moments ds) := by
  induction ds with
  | nil => simp [moments, translate]
  | cons d ds ih =>
    have hi := congrArg Moments.first ih
    have hj := congrArg Moments.second ih
    simp only [moments, translate] at hi hj
    apply Moments.ext
    · simp [moments, translate]
    · simp only [moments, translate, List.map_cons, List.sum_cons, List.length_cons]
      rw [hi]
      ring
    · simp only [moments, translate, List.map_cons, List.sum_cons, List.length_cons]
      rw [hj]
      ring

theorem moments_perm {xs ys : List ℕ} (h : xs.Perm ys) : moments xs = moments ys := by
  apply Moments.ext
  · exact h.length_eq
  · exact h.sum_eq
  · exact (h.map (fun (d : ℕ) => d ^ 2)).sum_eq

theorem enumBits_shift (depth start mask : ℕ) :
    enumBits depth start mask = (enumBits depth 0 mask).map (fun d => start + d) := by
  induction depth generalizing start mask with
  | zero => simp only [enumBits]; split <;> simp
  | succ depth ih =>
    simp only [enumBits]
    split
    · simp
    · rw [ih start, ih (start + 2 ^ depth), ih (0 + 2 ^ depth), List.map_append,
        List.map_map]
      simp only [Nat.zero_add, Function.comp_def, Nat.add_assoc]

theorem enumBits_mod_perm (depth start mask : ℕ) :
    (enumBits depth start (mask % 2 ^ (2 ^ depth))).Perm (enumBits depth start mask) := by
  apply (List.perm_ext_iff_of_nodup (enumBits_nodup _ _ _) (enumBits_nodup _ _ _)).mpr
  intro x
  simp only [mem_enumBits, Nat.testBit_mod_two_pow, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hlo, hhi, _, hb⟩
    exact ⟨hlo, hhi, hb⟩
  · rintro ⟨hlo, hhi, hb⟩
    exact ⟨hlo, hhi, by omega, hb⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem byteMoments_table : ∀ byte : Fin 256,
    byteMoments byte = moments (enumBits 3 0 byte) := by decide +kernel

theorem byteMoments_sound (mask : ℕ) :
    byteMoments (mask % 256) = moments (enumBits 3 0 mask) := by
  have h := byteMoments_table ⟨mask % 256, Nat.mod_lt _ (by decide)⟩
  have hm := moments_perm (enumBits_mod_perm 3 0 mask)
  norm_num only [Nat.reducePow] at hm
  exact h.trans hm

theorem fastMoments_sound (depth start mask : ℕ) :
    fastMoments depth start mask = moments (enumBits (depth + 3) start mask) := by
  induction depth generalizing start mask with
  | zero =>
    rw [fastMoments, byteMoments_sound, enumBits_shift 3 start mask, moments_shift]
  | succ depth ih =>
    change (if mask == 0 then _ else _) =
      moments (enumBits ((depth + 3) + 1) start mask)
    rw [enumBits]
    split
    · rfl
    · dsimp only
      rw [moments_append, ih, ih]

theorem windowMoments_sound (mask shift len : ℕ) :
    windowMoments mask shift len = moments (windowOffsets 13 mask shift len) := by
  rw [windowMoments, fastMoments_sound]
  change moments (enumBits 13 1 _) = _
  rw [enumBits_shift]
  simp only [windowOffsets, Nat.add_comm]

theorem stepFromMoments_eq (v a : ℕ) (ds : List ℕ) :
    stepFromMoments v a (moments ds) = momentStep v a ds := by
  rfl

theorem fastMomentStep_eq (v a mask shift len : ℕ) :
    fastMomentStep v a mask shift len =
      momentStep v a (windowOffsets 13 mask shift len) := by
  rw [fastMomentStep, windowMoments_sound, stepFromMoments_eq]

end RosserBitMoments

-- Source: Solutions/RosserScan.lean
/-!
Generic verifier for an interval. A shared bit mask covers all primes in the
interval; short blocks reuse windows of this mask. Successful execution is
proved to imply both the real inequality and the next reciprocal bound.
-/

namespace RosserScan

open RosserBitSieve AlternativeProductMoments RosserMomentBridge
open RosserLogCertificate RosserBlockCheck
open RosserBitMoments

theorem forceNat_eq {α : Type} (n : ℕ) (f : ℕ → α) : forceNat n f = f n := by
  cases n <;> rfl

def Covers (base top mask : ℕ) : Prop :=
  ∀ p, Nat.Prime p → base < p → p ≤ top → mask.testBit (p - (base + 1)) = true

theorem sieve_covers (divisors : List ℕ) (base top : ℕ)
    (hds : ∀ d ∈ divisors, 2 ≤ d ∧ d < base + 1) :
    Covers base top (candidateMask divisors (base + 1) (top - base)) := by
  intro p hp hlo hhi
  apply candidateMask_preserves_prime _ _ _ _ hds (by omega)
  simpa only [Nat.add_sub_of_le (show base + 1 ≤ p by omega)] using hp

def StepGood (a b w : ℕ) : Prop :=
  a < b ∧ (w : ℝ) / scale ≤ reciprocalProduct b ∧
    ∀ x : ℝ, (a : ℝ) ≤ x → x ≤ b → Bound x

theorem step_sound (base top mask a b v : ℕ)
    (hcover : Covers base top mask) (hbase : base ≤ a) (hbt : b ≤ top)
    (hv : (v : ℝ) / scale ≤ reciprocalProduct a)
    (hc : stepCheck a b v (stepOffsets base mask a b) = true) :
    StepGood a b (momentStep v a (stepOffsets base mask a b)) := by
  simp only [stepCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨ha, hab, hlen, hfirst, hupper⟩, hcheck⟩ := hc
  have hbounds : ∀ d ∈ stepOffsets base mask a b, 0 < d ∧ d ≤ b - a := by
    intro d hd
    have h := (mem_windowOffsets _ _ _ _ _).mp hd
    exact ⟨h.1, h.2.1⟩
  have hprimes : ∀ p, Nat.Prime p → a < p → p ≤ b →
      p - a ∈ stepOffsets base mask a b := by
    intro p hp hlo hhi
    apply (mem_windowOffsets _ _ _ _ _).mpr
    refine ⟨by omega, by omega, by omega, ?_⟩
    have he : p - a - 1 + (a - base) = p - (base + 1) := by omega
    rw [he]
    exact hcover p hp (by omega) (by omega)
  have hnext := momentStep_reciprocalProduct scale v a b _ scale_pos hab.le ha
    (windowOffsets_nodup _ _ _ _) hbounds hprimes hfirst hupper hv
  exact ⟨hab, hnext, fun x hax hxb => check_sound a b _ (by omega) hcheck hnext x hax hxb⟩

theorem stepData_eq (base mask a b v : ℕ) :
    stepData base mask a b v =
      (stepCheck a b v (stepOffsets base mask a b),
        momentStep v a (stepOffsets base mask a b)) := by
  unfold stepData
  rw [windowMoments_sound]
  rfl

theorem attempt_sound (base top mask a v fuel width b w : ℕ)
    (hcover : Covers base top mask) (hbase : base ≤ a)
    (hv : (v : ℝ) / scale ≤ reciprocalProduct a)
    (h : attempt base top mask a v fuel width = some (b, w)) :
    b ≤ top ∧ StepGood a b w := by
  induction fuel generalizing width with
  | zero => simp [attempt] at h
  | succ fuel ih =>
    simp only [attempt, stepData_eq] at h
    split at h
    · rename_i hc
      have he := Option.some.inj h
      have hb := congrArg Prod.fst he
      have hw := congrArg Prod.snd he
      dsimp only at hb hw
      subst b w
      exact ⟨min_le_left _ _, step_sound _ _ _ _ _ _ hcover hbase
        (min_le_left _ _) hv hc⟩
    · exact ih (width / 2) h

theorem run_sound (base top mask fuel a v w : ℕ)
    (hcover : Covers base top mask) (hbase : base ≤ a)
    (hv : (v : ℝ) / scale ≤ reciprocalProduct a)
    (h : run base top mask fuel a v = some w) :
    (w : ℝ) / scale ≤ reciprocalProduct top ∧
      ∀ x : ℝ, (a : ℝ) < x → x ≤ top → Bound x := by
  induction fuel generalizing a v with
  | zero =>
    simp only [run, forceNat_eq] at h
    split at h
    · rename_i ha
      have ha' : a = top := by simpa using ha
      have hv' : v = w := Option.some.inj h
      subst a w
      exact ⟨hv, by intro x hx hxt; linarith⟩
    · contradiction
  | succ fuel ih =>
    simp only [run, forceNat_eq] at h
    split at h
    · rename_i ha
      have ha' : a = top := by simpa using ha
      have hv' : v = w := Option.some.inj h
      subst a w
      exact ⟨hv, by intro x hx hxt; linarith⟩
    · split at h
      · contradiction
      · rename_i b w' htry
        have hs := attempt_sound base top mask a v 20 _ b w'
          hcover hbase hv htry
        have hab := hs.2.1
        have hi := ih b w' (by omega) hs.2.2.1 h
        refine ⟨hi.1, ?_⟩
        intro x hax hxt
        by_cases hxb : x ≤ b
        · exact hs.2.2.2 x hax.le hxb
        · exact hi.2 x (lt_of_not_ge hxb) hxt

end RosserScan

-- Source: Solutions/RosserPrefixBridge.lean
/-! Connect prime coverage of a block to the fast packed prefix counter. -/

namespace RosserPrefixBridge

open RosserPackedBarrier

theorem prime_card_le_candidateCount (a b n mask : ℕ)
    (han : a ≤ n) (hnb : n ≤ b)
    (hcover : ∀ p, Nat.Prime p → a < p → p ≤ b →
      mask.testBit (p - (a + 1)) = true) :
    (Nat.primesLE n \ Nat.primesLE a).card ≤
      candidateCount mask (n - a) := by
  let t := Nat.primesLE n \ Nat.primesLE a
  let s := (List.range (n - a)).filter (fun i => mask.testBit i)
  have hmap : Set.MapsTo (fun p : ℕ => p - (a + 1))
      (t : Set ℕ) (s.toFinset : Set ℕ) := by
    intro p hp
    obtain ⟨hpn, hpa⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hpn', hpprime⟩ := Nat.mem_primesLE.mp hpn
    have hap : a < p := by
      by_contra h
      exact hpa (Nat.mem_primesLE.mpr ⟨by omega, hpprime⟩)
    apply List.mem_toFinset.mpr
    apply List.mem_filter.mpr
    constructor
    · apply List.mem_range.mpr
      change p - (a + 1) < n - a
      omega
    · exact hcover p hpprime hap (by omega)
  have hinj : (t : Set ℕ).InjOn
      (fun p : ℕ => p - (a + 1)) := by
    intro p hp q hq heq
    have hp' := Finset.mem_sdiff.mp hp
    have hq' := Finset.mem_sdiff.mp hq
    have hpprime := (Nat.mem_primesLE.mp hp'.1).2
    have hqprime := (Nat.mem_primesLE.mp hq'.1).2
    have hap : a < p := by
      by_contra h
      exact hp'.2 (Nat.mem_primesLE.mpr ⟨by omega, hpprime⟩)
    have haq : a < q := by
      by_contra h
      exact hq'.2 (Nat.mem_primesLE.mpr ⟨by omega, hqprime⟩)
    change p - (a + 1) = q - (a + 1) at heq
    omega
  have hc := Finset.card_le_card_of_injOn (fun p : ℕ => p - (a + 1)) hmap hinj
  have hs : s.toFinset.card ≤ s.length := List.toFinset_card_le s
  have hfinal := hc.trans hs
  simpa only [t, s, candidateCount] using hfinal

theorem packed_affine_count (a : ℕ) (x : ℝ) (mask len intercept slope : ℕ)
    (hlen : 0 < len) (hm : mask < 2 ^ len) (hI : 0 < intercept)
    (hcount : 16384 * candidateCount mask len < 2 ^ 31)
    (hrhs : (intercept - 1) + slope *
      (32 * ((len + 31) / 32 - 1)) < 2 ^ 31)
    (hcheck : packedCheck mask len (intercept - 1) slope = true)
    (hax : (a : ℝ) ≤ x)
    (hfloor : ⌊x⌋₊ ≤ a + len) :
    (candidateCount mask (⌊x⌋₊ - a) : ℝ) <
      (intercept : ℝ) / 16384 +
      (slope : ℝ) / 16384 * (x - a) := by
  have han : a ≤ ⌊x⌋₊ := Nat.le_floor hax
  have hlen' : ⌊x⌋₊ - a ≤ len := by omega
  have hb := packedCheck_sound mask len (intercept - 1) slope
    hlen hm hcount hrhs hcheck (⌊x⌋₊ - a) hlen'
  let pos := 32 * ((⌊x⌋₊ - a - 1) / 32)
  have hpos : pos ≤ ⌊x⌋₊ - a := by dsimp [pos]; omega
  have hfl : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith only [hax])
  have hposreal : (pos : ℝ) ≤ x - a := by
    have hsub : ((⌊x⌋₊ - a : ℕ) : ℝ) = (⌊x⌋₊ : ℝ) - a :=
      Nat.cast_sub han
    have hposcast : (pos : ℝ) ≤ (⌊x⌋₊ - a : ℕ) := by exact_mod_cast hpos
    exact hposcast.trans (by rw [hsub]; linarith only [hfl])
  have hraw : 16384 * candidateCount mask (⌊x⌋₊ - a) <
      intercept + slope * pos := by
    have hb' : 16384 * candidateCount mask (⌊x⌋₊ - a) ≤
        (intercept - 1) + slope * pos := by
      simpa only [pos, Nat.mul_assoc] using hb
    omega
  have hraw' : (16384 : ℝ) * candidateCount mask (⌊x⌋₊ - a) <
      (intercept : ℝ) + slope * pos := by exact_mod_cast hraw
  have hsl : (slope : ℝ) * pos ≤ slope * (x - a) :=
    mul_le_mul_of_nonneg_left hposreal (by positivity)
  have htarget : (16384 : ℝ) * candidateCount mask (⌊x⌋₊ - a) <
      (intercept : ℝ) + slope * (x - a) := by
    linarith only [hraw', hsl]
  have heq : (intercept : ℝ) / 16384 +
      (slope : ℝ) / 16384 * (x - a) =
      ((intercept : ℝ) + slope * (x - a)) / 16384 := by ring
  rw [heq]
  apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 16384)).mpr
  simpa only [mul_comm] using htarget

theorem block_sound (a b v mask : ℕ)
    (hvalid : (RosserPrefixParams.parameters a b v).valid = true)
    (hm : mask < 2 ^ (b - a))
    (hI : 0 < (RosserPrefixParams.parameters a b v).intercept)
    (hcount : 16384 * candidateCount mask (b - a) < 2 ^ 31)
    (hrhs :
      ((RosserPrefixParams.parameters a b v).intercept - 1) +
        (RosserPrefixParams.parameters a b v).slope *
          (32 * (((b - a) + 31) / 32 - 1)) < 2 ^ 31)
    (hcheck : packedCheck mask (b - a)
      ((RosserPrefixParams.parameters a b v).intercept - 1)
      (RosserPrefixParams.parameters a b v).slope = true)
    (hcover : ∀ p, Nat.Prime p → a < p → p ≤ b →
      mask.testBit (p - (a + 1)) = true)
    (hv : ((v : ℝ) / RosserLogCertificate.scale) ≤
      RosserMomentBridge.reciprocalProduct a)
    (x : ℝ) (hax : (a : ℝ) ≤ x) (hxb : x ≤ b) :
    RosserBlockCheck.Bound x := by
  have hab := (RosserPrefixParams.parameters_valid a b v hvalid).2.1
  have hlen : 0 < b - a := by omega
  have hfloor : ⌊x⌋₊ ≤ b := Nat.floor_le_of_le hxb
  have hfloor' : ⌊x⌋₊ ≤ a + (b - a) := by omega
  have hcard := prime_card_le_candidateCount a b ⌊x⌋₊ mask
    (Nat.le_floor hax) hfloor hcover
  have hprefix := packed_affine_count a x mask (b - a)
    (RosserPrefixParams.parameters a b v).intercept
    (RosserPrefixParams.parameters a b v).slope
    hlen hm hI hcount hrhs hcheck hax hfloor'
  exact RosserPrefixParams.parameterized_bound a b v
    (candidateCount mask (⌊x⌋₊ - a)) x hvalid hax hxb hv hcard hprefix

theorem window_mask_covers (base top mask a b : ℕ)
    (hcover : RosserScan.Covers base top mask)
    (hbase : base ≤ a) (hbt : b ≤ top) :
    ∀ p, Nat.Prime p → a < p → p ≤ b →
      ((mask / 2 ^ (a - base)) % 2 ^ (b - a)).testBit
        (p - (a + 1)) = true := by
  intro p hp hap hpb
  have hi : p - (a + 1) < b - a := by omega
  have heq : p - (a + 1) + (a - base) = p - (base + 1) := by omega
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  simp only [show decide (p - (a + 1) < b - a) = true by simp [hi],
    Bool.true_and, heq]
  exact hcover p hp (by omega) (by omega)

end RosserPrefixBridge

-- Source: Solutions/RosserSieveData.lean
/-! Sieve divisors are untrusted numerical hints. Their only required property
is the elementary range check below; their primality is not assumed. -/
namespace RosserSieveData
open RosserBitSieve RosserScan RosserMomentBridge RosserLogCertificate

theorem divisors_ge_two : ∀ d ∈ divisors, 2 ≤ d := by decide +kernel

theorem smallDivisors_bounds (base : ℕ) :
    ∀ d ∈ smallDivisors base, 2 ≤ d ∧ d < base + 1 := by
  intro d hd
  obtain ⟨hd, hle⟩ := List.mem_filter.mp hd
  exact ⟨divisors_ge_two d hd, by have := of_decide_eq_true hle; omega⟩

theorem segment_sound (base top v w : ℕ)
    (hv : (v : ℝ) / scale ≤ reciprocalProduct base)
    (h : segment base top v = some w) :
    (w : ℝ) / scale ≤ reciprocalProduct top ∧
      ∀ x : ℝ, (base : ℝ) < x → x ≤ top → RosserBlockCheck.Bound x := by
  simp only [segment, forceNat_eq] at h
  exact run_sound base top (mask base top) 4096 base v w
    (sieve_covers _ _ _ (smallDivisors_bounds base)) (le_refl _) hv h

end RosserSieveData

-- Source: Solutions/RosserCachedSieve.lean
/-! A reusable table of periodic divisor masks for the fixed-size segments. -/

namespace RosserCachedSieve

open RosserBitSieve RosserScan

def withMasks {α : Type} (len : ℕ) : List ℕ → (List (ℕ × ℕ) → α) → α
  | [], f => f []
  | d :: ds, f =>
    forceNat (periodicMask d ((len + d - 1) / d)) fun m =>
      withMasks len ds fun rest => f ((d, m) :: rest)

def pairs (len : ℕ) (ds : List ℕ) : List (ℕ × ℕ) :=
  ds.map (fun d => (d, periodicMask d ((len + d - 1) / d)))

theorem withMasks_eq {α : Type} (len : ℕ) (ds : List ℕ)
    (f : List (ℕ × ℕ) → α) : withMasks len ds f = f (pairs len ds) := by
  induction ds generalizing f with
  | nil => rfl
  | cons d ds ih =>
    simp only [withMasks, RosserScan.forceNat_eq, ih, pairs, List.map_cons]

def mask (ds : List (ℕ × ℕ)) (base top : ℕ) : ℕ :=
  let len := top - base
  let composite := ds.foldl (fun acc dm =>
    if dm.1 ≤ base then
      acc ||| (dm.2 * 2 ^ ((dm.1 - (base + 1) % dm.1) % dm.1))
    else acc) 0
  (2 ^ len - 1) ^^^ (composite % 2 ^ len)

theorem mask_lt (ds : List (ℕ × ℕ)) (base top : ℕ) :
    mask ds base top < 2 ^ (top - base) := by
  unfold mask
  apply Nat.xor_lt_two_pow
  · exact Nat.sub_lt (by positivity) (by norm_num)
  · exact Nat.mod_lt _ (by positivity)

theorem pairs_fold_eq (fixedLen base : ℕ) (ds : List ℕ) (acc : ℕ) :
    (pairs fixedLen ds).foldl (fun acc dm =>
      if dm.1 ≤ base then
        acc ||| (dm.2 * 2 ^ ((dm.1 - (base + 1) % dm.1) % dm.1))
      else acc) acc =
    (ds.filter (fun d => decide (d ≤ base))).foldl (fun acc d =>
      acc ||| divisorMask (base + 1) fixedLen d) acc := by
  induction ds generalizing acc with
  | nil => rfl
  | cons d ds ih =>
    simp only [pairs, List.map_cons, List.foldl_cons, List.filter_cons]
    by_cases hd : d ≤ base
    · simp only [hd, decide_true, if_true]
      change (pairs fixedLen ds).foldl _
        (acc ||| divisorMask (base + 1) fixedLen d) = _
      exact ih _
    · simp only [hd, decide_false, Bool.false_eq_true, if_false]
      exact ih _

theorem mask_prime (fixedLen base top : ℕ) (ds : List ℕ)
    (hds : ∀ d ∈ ds, 2 ≤ d) (hbase : base < top)
    (hlen : top - base ≤ fixedLen) :
    ∀ p, Nat.Prime p → base < p → p ≤ top →
      (mask (pairs fixedLen ds) base top).testBit (p - (base + 1)) = true := by
  intro p hp hbp hpt
  let small := ds.filter (fun d => decide (d ≤ base))
  have hsmall : ∀ d ∈ small, 2 ≤ d ∧ d < base + 1 := by
    intro d hd
    obtain ⟨hdmem, hdle⟩ := List.mem_filter.mp hd
    exact ⟨hds d hdmem, by have := of_decide_eq_true hdle; omega⟩
  have hi : p - (base + 1) < top - base := by omega
  have hprim : Nat.Prime ((base + 1) + (p - (base + 1))) := by
    simpa only [Nat.add_sub_of_le (by omega : base + 1 ≤ p)] using hp
  have hcomp := compositeMask_preserves_prime small (base + 1) fixedLen
    (p - (base + 1)) hsmall hprim
  unfold mask
  rw [pairs_fold_eq]
  change ((2 ^ (top - base) - 1) ^^^
    (compositeMask small (base + 1) fixedLen % 2 ^ (top - base))).testBit
      (p - (base + 1)) = true
  simp [Nat.testBit_xor, Nat.testBit_two_pow_sub_one,
    Nat.testBit_mod_two_pow, hi, hcomp]

end RosserCachedSieve

-- Source: Solutions/RosserFastStep.lean
/-! Generic soundness of a fast finite block once its moments and bit mask
have been certified. -/

namespace RosserFastStep

open RosserBitSieve RosserBitMoments RosserMomentBridge
open RosserPrefixBridge RosserPackedBarrier RosserLogCertificate
open AlternativeProductMoments

theorem step_sound (a b v mask depth : ℕ) (s : Moments)
    (hvalid : (RosserPrefixParams.parameters a b v).valid = true)
    (hm : mask < 2 ^ (b - a))
    (hdepth : b - a ≤ 2 ^ depth)
    (hcover : ∀ p, Nat.Prime p → a < p → p ≤ b →
      mask.testBit (p - (a + 1)) = true)
    (hmom : s = moments (windowOffsets depth mask 0 (b - a)))
    (hfirst : s.first ≤ s.count * a)
    (hupper : s.count * a ^ 2 - a * s.first + s.second ≤ a ^ 3)
    (hI : 0 < (RosserPrefixParams.parameters a b v).intercept)
    (hcount : 16384 * candidateCount mask (b - a) < 2 ^ 31)
    (hrhs : ((RosserPrefixParams.parameters a b v).intercept - 1) +
      (RosserPrefixParams.parameters a b v).slope *
        (32 * (((b - a) + 31) / 32 - 1)) < 2 ^ 31)
    (hcheck : packedCheck mask (b - a)
      ((RosserPrefixParams.parameters a b v).intercept - 1)
      (RosserPrefixParams.parameters a b v).slope = true)
    (hv : ((v : ℝ) / scale) ≤ reciprocalProduct a) :
    ((stepFromMoments v a s : ℝ) / scale ≤ reciprocalProduct b) ∧
      ∀ x : ℝ, (a : ℝ) ≤ x → x ≤ b → RosserBlockCheck.Bound x := by
  have hab := (RosserPrefixParams.parameters_valid a b v hvalid).2.1
  have ha : 2 ≤ a := by
    have ha' := (RosserPrefixParams.parameters_valid a b v hvalid).1
    omega
  let ds := windowOffsets depth mask 0 (b - a)
  have hnodup : ds.Nodup := windowOffsets_nodup depth mask 0 (b - a)
  have hbounds : ∀ d ∈ ds, 0 < d ∧ d ≤ b - a := by
    intro d hd
    have hb := (mem_windowOffsets depth mask 0 (b - a) d).mp hd
    exact ⟨hb.1, hb.2.1⟩
  have hprimes : ∀ p, Nat.Prime p → a < p → p ≤ b → p - a ∈ ds := by
    intro p hp hap hpb
    apply (mem_windowOffsets depth mask 0 (b - a) (p - a)).mpr
    refine ⟨by omega, by omega, by omega, ?_⟩
    have heq : p - a - 1 + 0 = p - (a + 1) := by omega
    rw [heq]
    exact hcover p hp hap hpb
  have hfirst' : firstMoment ds ≤ ds.length * a := by
    simpa only [hmom, moments, firstMoment] using hfirst
  have hupper' : upperNumerator a ds ≤ a ^ 3 := by
    simpa only [hmom, moments, upperNumerator, firstMoment,
      secondMoment] using hupper
  have hnext := momentStep_reciprocalProduct scale v a b ds scale_pos hab.le ha
    hnodup hbounds hprimes hfirst' hupper' hv
  have heq : stepFromMoments v a s = momentStep v a ds := by
    rw [hmom]
    exact stepFromMoments_eq v a ds
  refine ⟨by simpa only [heq] using hnext, ?_⟩
  intro x hax hxb
  exact block_sound a b v mask hvalid hm hI hcount hrhs hcheck
    hcover hv x hax hxb

end RosserFastStep

-- Source: Solutions/RosserPackedMomentsSound.lean
/-! Correctness of packed first and second moments. -/

namespace RosserPackedMoments

open RosserBitMoments RosserScan

def strictMoments {α : Type} (s : Moments) (f : Moments → α) : α :=
  forceNat s.count fun c => forceNat s.first fun a => forceNat s.second fun b =>
    f ⟨c, a, b⟩

def bytes (mask stripe : Nat) : Nat → Moments → Moments
  | 0, s => s
  | j + 1, s =>
    forceNat ((mask >>> j) &&& stripe) fun bit =>
      strictMoments ⟨s.count + bit, s.first + j * bit, s.second + j * j * bit⟩
        (bytes mask stripe j)

def combine (bits half : Nat) (s : Moments) : Moments :=
  let stripe := RosserBitSieve.periodicMask (2 * half) (bits / (2 * half)) *
    (2 ^ half - 1)
  forceNat stripe fun stripe =>
  forceNat ((s.count >>> half) &&& stripe) fun cr =>
  forceNat ((s.first >>> half) &&& stripe) fun fr =>
    ⟨(s.count &&& stripe) + cr,
     (s.first &&& stripe) + fr + half * cr,
     (s.second &&& stripe) + ((s.second >>> half) &&& stripe) +
       2 * half * fr + half * half * cr⟩

def reduce (bits : Nat) : Nat → Nat → Moments → Moments
  | 0, _, s => s
  | fuel + 1, half, s =>
    strictMoments (combine bits half s) (reduce bits fuel (2 * half))

def packedMoments (depth mask : Nat) : Moments :=
  let bits := 2 ^ (depth + 3)
  forceNat (RosserBitSieve.periodicMask 8 (bits / 8)) fun stripe =>
    strictMoments (bytes mask stripe 8 ⟨0, 0, 0⟩) fun s =>
      translate 1 (reduce bits depth 8 s)



open RosserPackedBarrier

theorem strictMoments_eq {α : Type} (s : Moments) (f : Moments → α) :
    strictMoments s f = f s := by
  cases s
  simp only [strictMoments, RosserPackedBarrier.forceNat_eq]

def packed (w n : ℕ) (f : ℕ → Moments) : Moments :=
  ⟨pack (2 ^ w) n (fun i => (f i).count),
   pack (2 ^ w) n (fun i => (f i).first),
   pack (2 ^ w) n (fun i => (f i).second)⟩

def lane (mask w i : ℕ) : Moments :=
  ⟨∑ j ∈ Finset.range w, bitValue mask (w * i + j),
   ∑ j ∈ Finset.range w, j * bitValue mask (w * i + j),
   ∑ j ∈ Finset.range w, j * j * bitValue mask (w * i + j)⟩

theorem pair_extract (w n : ℕ) (hw : 0 < w) (f : ℕ → ℕ)
    (hf : ∀ i < 2 * n, f i < 2 ^ w) :
    let stripe := pack (2 ^ (2 * w)) n (fun _ => 2 ^ w - 1)
    (pack (2 ^ w) (2 * n) f &&& stripe =
      pack (2 ^ (2 * w)) n (fun i => f (2 * i))) ∧
    ((pack (2 ^ w) (2 * n) f >>> w) &&& stripe =
      pack (2 ^ (2 * w)) n (fun i => f (2 * i + 1))) := by
  dsimp only
  have hq : 0 < 2 ^ w := by positivity
  have hpow : 2 ^ w * 2 ^ w = 2 ^ (2 * w) := by rw [two_mul, pow_add]
  let g := fun i => f (2 * i) + 2 ^ w * f (2 * i + 1)
  have hg : ∀ i < n, g i < 2 ^ (2 * w) := by
    intro i hi
    have h0 := hf (2 * i) (by omega)
    have h1 := hf (2 * i + 1) (by omega)
    dsimp [g]
    rw [← hpow]
    nlinarith
  have hm : ∀ i < n, 2 ^ w - 1 < 2 ^ (2 * w - w) := by
    intro i hi
    rw [show 2 * w - w = w by omega]
    omega
  rw [pack_pair, hpow]
  change (_ &&& _) = _ ∧ (_ >>> w &&& _) = _
  constructor
  · rw [pack_and (2 * w) n (by omega) g _ hg (fun i hi => (hm i hi).trans_le
      (Nat.pow_le_pow_right (by omega) (by omega)))]
    apply pack_congr
    intro i hi
    simp only [g, Nat.and_two_pow_sub_one_eq_mod, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (hf (2 * i) (by omega))]
  · rw [pack_shift_and (2 * w) n w (by omega) (by omega) g _ hg hm]
    apply pack_congr
    intro i hi
    simp only [g, Nat.shiftRight_eq_div_pow, Nat.add_mul_div_left _ _ hq,
      Nat.div_eq_of_lt (hf (2 * i) (by omega)), Nat.zero_add,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (hf (2 * i + 1) (by omega))]

theorem combine_sound (w n : ℕ) (hw : 0 < w) (f : ℕ → Moments)
    (hc : ∀ i < 2 * n, (f i).count < 2 ^ w)
    (hf : ∀ i < 2 * n, (f i).first < 2 ^ w)
    (hs : ∀ i < 2 * n, (f i).second < 2 ^ w) :
    combine (2 * w * n) w (packed w (2 * n) f) =
      packed (2 * w) n (fun i => merge (f (2 * i)) (translate w (f (2 * i + 1)))) := by
  have hstripe : RosserBitSieve.periodicMask (2 * w) ((2 * w * n) / (2 * w)) *
      (2 ^ w - 1) = pack (2 ^ (2 * w)) n (fun _ => 2 ^ w - 1) := by
    rw [Nat.mul_div_cancel_left _ (by omega), pack_const]
    unfold RosserBitSieve.periodicMask
    rw [pack_const_one _ _ (Nat.one_lt_two_pow (by omega)), pow_mul]
    ring
  obtain ⟨hcl, hcr⟩ := pair_extract w n hw (fun i => (f i).count) hc
  obtain ⟨hfl, hfr⟩ := pair_extract w n hw (fun i => (f i).first) hf
  obtain ⟨hsl, hsr⟩ := pair_extract w n hw (fun i => (f i).second) hs
  simp only [combine, RosserPackedBarrier.forceNat_eq, hstripe, packed]
  rw [hcl, hcr, hfl, hfr, hsl, hsr]
  apply Moments.ext <;> simp only [merge, translate, pack_add, pack_mul] <;> ring

theorem lane_pair (mask w i : ℕ) :
    lane mask (2 * w) i = merge (lane mask w (2 * i))
      (translate w (lane mask w (2 * i + 1))) := by
  apply Moments.ext
  · exact blockSum_pair (bitValue mask) w i
  · simp only [lane, merge, translate]
    rw [show 2 * w = w + w by omega, Finset.sum_range_add]
    have hpos : ∀ j : ℕ, (w + w) * i + (w + j) = w * (2 * i + 1) + j := by
      intro j; ring
    have hpos' : ∀ j : ℕ, (w + w) * i + j = w * (2 * i) + j := by
      intro j; ring
    simp only [hpos, hpos']
    have hsum :
        (∑ j ∈ Finset.range w, (w + j) * bitValue mask (w * (2 * i + 1) + j)) =
        w * (∑ j ∈ Finset.range w, bitValue mask (w * (2 * i + 1) + j)) +
        (∑ j ∈ Finset.range w, j * bitValue mask (w * (2 * i + 1) + j)) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hsum]
    ring
  · simp only [lane, merge, translate]
    rw [show 2 * w = w + w by omega, Finset.sum_range_add]
    have hpos : ∀ j : ℕ, (w + w) * i + (w + j) = w * (2 * i + 1) + j := by
      intro j; ring
    have hpos' : ∀ j : ℕ, (w + w) * i + j = w * (2 * i) + j := by
      intro j; ring
    simp only [hpos, hpos']
    have hsum :
        (∑ j ∈ Finset.range w, (w + j) * (w + j) * bitValue mask (w * (2 * i + 1) + j)) =
        (∑ j ∈ Finset.range w, j * j * bitValue mask (w * (2 * i + 1) + j)) +
        2 * w * (∑ j ∈ Finset.range w, j * bitValue mask (w * (2 * i + 1) + j)) +
        w * w * (∑ j ∈ Finset.range w, bitValue mask (w * (2 * i + 1) + j)) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hsum]
    ring

theorem bytes_eq (mask stripe j : ℕ) (s : Moments) :
    bytes mask stripe j s =
      ⟨s.count + ∑ i ∈ Finset.range j, ((mask >>> i) &&& stripe),
       s.first + ∑ i ∈ Finset.range j, i * ((mask >>> i) &&& stripe),
       s.second + ∑ i ∈ Finset.range j, i * i * ((mask >>> i) &&& stripe)⟩ := by
  induction j generalizing s with
  | zero => simp [bytes]
  | succ j ih =>
    simp only [bytes, RosserPackedBarrier.forceNat_eq, strictMoments_eq, ih, Finset.sum_range_succ]
    apply Moments.ext <;> dsimp only <;> ring

theorem pack_sum (q n terms : ℕ) (f : ℕ → ℕ → ℕ) :
    pack q n (fun i => ∑ j ∈ Finset.range terms, f i j) =
      ∑ j ∈ Finset.range terms, pack q n (fun i => f i j) := by
  induction terms with
  | zero => simp only [Finset.range_zero, Finset.sum_empty]; rw [pack_const q n 0]; simp
  | succ terms ih => simp only [Finset.sum_range_succ, pack_add, ih]

theorem byte_plane (mask n j : ℕ) (hj : j < 8) (hm : mask < 2 ^ (8 * n)) :
    ((mask >>> j) &&& RosserBitSieve.periodicMask 8 n) =
      pack 256 n (fun i => bitValue mask (8 * i + j)) := by
  let f := fun i => mask / 2 ^ (8 * i) % 2 ^ 8
  have hf : ∀ i < n, f i < 2 ^ 8 := fun i hi => Nat.mod_lt _ (by positivity)
  have hp : pack (2 ^ 8) n f = mask := pack_digits 8 n mask (by omega) hm
  have hs : RosserBitSieve.periodicMask 8 n = pack (2 ^ 8) n (fun _ => 1) := by
    unfold RosserBitSieve.periodicMask
    rw [pack_const_one _ _ (by norm_num), pow_mul]
  rw [← hp, hs, pack_shift_and 8 n j (by omega) (by omega) f _ hf
    (fun i hi => Nat.one_lt_two_pow (by omega))]
  have hbase : (2 ^ 8 : ℕ) = 256 := by norm_num
  rw [hbase]
  apply pack_congr
  intro i hi
  have hb := pack_testBit 8 n i j hf hi hj
  rw [hp] at hb
  simp only [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rw [← bitValue_eq_digit]
  rw [← hbase, hp]
  exact (congrArg Bool.toNat hb).symm

theorem bytes_sound (mask n : ℕ) (hm : mask < 2 ^ (8 * n)) :
    bytes mask (RosserBitSieve.periodicMask 8 n) 8 ⟨0, 0, 0⟩ =
      packed 8 n (lane mask 8) := by
  rw [bytes_eq]
  apply Moments.ext <;> simp only [packed, lane, Nat.zero_add, pack_sum]
  · apply Finset.sum_congr rfl
    intro j hj
    exact byte_plane mask n j (Finset.mem_range.mp hj) hm
  · apply Finset.sum_congr rfl
    intro j hj
    rw [byte_plane mask n j (Finset.mem_range.mp hj) hm, pack_mul]
    norm_num
  · apply Finset.sum_congr rfl
    intro j hj
    rw [byte_plane mask n j (Finset.mem_range.mp hj) hm, pack_mul]
    norm_num


def laneBudget (w : ℕ) : ℕ := ∑ j ∈ Finset.range w, (j + 1) ^ 2

theorem lane_le_budget (mask w i : ℕ) :
    (lane mask w i).count ≤ laneBudget w ∧
    (lane mask w i).first ≤ laneBudget w ∧
    (lane mask w i).second ≤ laneBudget w := by
  have hb := fun j => bitValue_le_one mask (w * i + j)
  dsimp only [lane, laneBudget]
  constructor
  · apply Finset.sum_le_sum
    intro j hj
    exact (hb j).trans (Nat.succ_le_of_lt (by positivity))
  constructor
  · apply Finset.sum_le_sum
    intro j hj
    have := hb j
    nlinarith
  · apply Finset.sum_le_sum
    intro j hj
    have h := Nat.mul_le_mul_left (j * j) (hb j)
    simp only [Nat.mul_one] at h
    nlinarith

theorem laneBudget_le_cube (w : ℕ) : laneBudget w ≤ w ^ 3 := by
  calc
    laneBudget w ≤ ∑ j ∈ Finset.range w, w ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      have h := Finset.mem_range.mp hj
      exact Nat.pow_le_pow_left (by omega) 2
    _ = w ^ 3 := by simp; ring

theorem triple_lt_power (d : ℕ) : 3 * (d + 4) < 2 ^ (d + 4) := by
  induction d with
  | zero => norm_num
  | succ d ih =>
    rw [show d + 1 + 4 = (d + 4) + 1 by omega, pow_succ]
    omega

theorem laneBudget_lt (d : ℕ) : laneBudget (2 ^ (d + 3)) < 2 ^ (2 ^ (d + 3)) := by
  cases d with
  | zero => decide
  | succ d =>
    have h := laneBudget_le_cube (2 ^ (d + 4))
    have hp : (2 ^ (d + 4)) ^ 3 < 2 ^ (2 ^ (d + 4)) := by
      rw [← pow_mul]
      apply Nat.pow_lt_pow_right (by omega)
      simpa only [Nat.mul_comm] using triple_lt_power d
    simpa only [Nat.add_assoc] using h.trans_lt hp

theorem packed_congr (w n : ℕ) {f g : ℕ → Moments}
    (h : ∀ i < n, f i = g i) : packed w n f = packed w n g := by
  apply Moments.ext <;> apply pack_congr <;> intro i hi <;> rw [h i hi]

theorem combine_lane (d n mask : ℕ) :
    combine (2 * 2 ^ (d + 3) * n) (2 ^ (d + 3))
      (packed (2 ^ (d + 3)) (2 * n) (lane mask (2 ^ (d + 3)))) =
      packed (2 * 2 ^ (d + 3)) n (lane mask (2 * 2 ^ (d + 3))) := by
  have hb := laneBudget_lt d
  rw [combine_sound _ _ (by positivity) _
    (fun i hi => ((lane_le_budget mask _ i).1).trans_lt hb)
    (fun i hi => ((lane_le_budget mask _ i).2.1).trans_lt hb)
    (fun i hi => ((lane_le_budget mask _ i).2.2).trans_lt hb)]
  apply packed_congr
  intro i hi
  exact (lane_pair mask _ i).symm

theorem reduce_sound (fuel d mask : ℕ) :
    reduce (2 ^ (fuel + d + 3)) fuel (2 ^ (d + 3))
      (packed (2 ^ (d + 3)) (2 ^ fuel) (lane mask (2 ^ (d + 3)))) =
      lane mask (2 ^ (fuel + d + 3)) 0 := by
  induction fuel generalizing d with
  | zero => simp [reduce, packed, pack]
  | succ fuel ih =>
    have hbits : 2 ^ (fuel + 1 + d + 3) = 2 * 2 ^ (d + 3) * 2 ^ fuel := by
      rw [show fuel + 1 + d + 3 = 1 + (d + 3) + fuel by omega]
      simp only [pow_add, pow_one]
    have hnext : 2 * 2 ^ (d + 3) = 2 ^ ((d + 1) + 3) := by
      rw [show d + 1 + 3 = 1 + (d + 3) by omega]
      simp only [pow_add, pow_one]
    simp only [reduce, strictMoments_eq]
    rw [hbits, show 2 ^ (fuel + 1) = 2 * 2 ^ fuel by rw [pow_succ]; omega,
      combine_lane, hnext]
    rw [← pow_add]
    convert ih (d + 1) using 1 <;> congr 2 <;> omega

theorem moments_filter_range (mask w : ℕ) :
    moments ((List.range w).filter (fun i => mask.testBit i)) = lane mask w 0 := by
  induction w with
  | zero => simp [moments, lane]
  | succ w ih =>
    have hc := congrArg Moments.count ih
    have hf := congrArg Moments.first ih
    have hs := congrArg Moments.second ih
    simp only [moments, lane, Nat.mul_zero, Nat.zero_add] at hc hf hs
    apply Moments.ext <;>
      simp only [moments, List.range_succ, List.filter_append,
        List.length_append, List.sum_append, List.map_append, lane,
        Nat.mul_zero, Nat.zero_add, Finset.sum_range_succ]
    · rw [hc]
      cases h : mask.testBit w <;> simp [List.filter, h, bitValue]
    · rw [hf]
      cases h : mask.testBit w <;> simp [List.filter, h, bitValue]
    · rw [hs]
      cases h : mask.testBit w <;> simp [List.filter, h, bitValue, pow_two]

theorem enumBits_perm_filter (depth mask : ℕ) :
    (RosserBitSieve.enumBits depth 0 mask).Perm
      ((List.range (2 ^ depth)).filter (fun i => mask.testBit i)) := by
  apply (List.perm_ext_iff_of_nodup (RosserBitSieve.enumBits_nodup _ _ _)
    ((List.nodup_range).filter _)).mpr
  intro x
  simp only [RosserBitSieve.mem_enumBits, Nat.zero_le, Nat.zero_add, Nat.sub_zero,
    true_and, List.mem_filter, List.mem_range]

theorem lane_eq_moments (depth mask : ℕ) :
    lane mask (2 ^ depth) 0 = moments (RosserBitSieve.enumBits depth 0 mask) := by
  rw [moments_perm (enumBits_perm_filter depth mask), moments_filter_range]

/-- All three SWAR moments are exactly the moments of the selected offsets. -/
theorem packedMoments_sound (depth mask : ℕ) (hm : mask < 2 ^ (2 ^ (depth + 3))) :
    packedMoments depth mask =
      moments (RosserBitSieve.enumBits (depth + 3) 1 mask) := by
  have hbits : 2 ^ (depth + 3) = 8 * 2 ^ depth := by
    rw [pow_add]
    norm_num
    omega
  have hdiv : 2 ^ (depth + 3) / 8 = 2 ^ depth := by
    rw [hbits, Nat.mul_div_cancel_left _ (by omega)]
  have hmask : mask < 2 ^ (8 * 2 ^ depth) := by rwa [← hbits]
  simp only [packedMoments, RosserPackedBarrier.forceNat_eq, strictMoments_eq, hdiv]
  rw [bytes_sound mask (2 ^ depth) hmask]
  have hr := reduce_sound depth 0 mask
  simp only [Nat.add_zero, Nat.zero_add] at hr
  norm_num only [Nat.reducePow] at hr
  rw [hr, lane_eq_moments, enumBits_shift (depth + 3) 1 mask, moments_shift]

/-- Padding a mask adds no selected offsets. -/
theorem candidateCount_eq_enumBits_length (depth mask len : ℕ)
    (hm : mask < 2 ^ len) (hlen : len ≤ 2 ^ (depth + 3)) :
    candidateCount mask len = (RosserBitSieve.enumBits (depth + 3) 1 mask).length := by
  rw [enumBits_shift, List.length_map]
  rw [← candidateCount_pad mask len (2 ^ (depth + 3)) hm hlen]
  exact (enumBits_perm_filter (depth + 3) mask).length_eq.symm

theorem packedMoments_eq_fastMoments (depth mask : ℕ)
    (hm : mask < 2 ^ (2 ^ (depth + 3))) :
    packedMoments depth mask = fastMoments depth 1 mask := by
  rw [packedMoments_sound depth mask hm, fastMoments_sound]

#print axioms packedMoments_sound
#print axioms candidateCount_eq_enumBits_length

end RosserPackedMoments

-- Source: Solutions/RosserFastCompute.lean
/-! The fast numerical block verifier, parameterized by a certified moments
implementation. -/

namespace RosserFastCompute

open RosserScan RosserBitMoments RosserPackedBarrier
open RosserPrefixParams RosserLogCertificate

def strictMoments {α : Type} (s : Moments) (f : Moments → α) : α :=
  forceNat s.count fun c => forceNat s.first fun u => forceNat s.second fun t =>
    f ⟨c, u, t⟩

theorem strictMoments_eq {α : Type} (s : Moments) (f : Moments → α) :
    strictMoments s f = f s := by
  cases s with
  | mk c u t => simp only [strictMoments, RosserScan.forceNat_eq]

def depthFor (len : ℕ) : ℕ :=
  if len ≤ 8 then 0 else Nat.log2 ((len - 1) / 8) + 1

def stepWith (mom : ℕ → ℕ → Moments) (mask a b v : ℕ) : Option ℕ :=
  let len := b - a
  let depth := depthFor len
  strictMoments (mom depth mask) fun s =>
  let par := parameters a b v
  forceNat par.intercept fun intercept =>
  forceNat par.slope fun slope =>
    if par.valid && decide (0 < intercept ∧
      16384 * s.count < 2 ^ 31 ∧
      intercept + slope * (32 * ((len + 31) / 32 - 1)) < 2 ^ 31 ∧
      mask < 2 ^ len ∧ len ≤ 2 ^ (depth + 3) ∧
      s.first ≤ s.count * a ∧
      s.count * a ^ 2 - a * s.first + s.second ≤ a ^ 3) &&
      packedCheck mask len (intercept - 1) slope then
        some (stepFromMoments v a s)
    else none

theorem windowOffsets_eq_enumBits (depth mask len : ℕ) (hm : mask < 2 ^ len) :
    RosserBitSieve.windowOffsets (depth + 3) mask 0 len =
      RosserBitSieve.enumBits (depth + 3) 1 mask := by
  simp only [RosserBitSieve.windowOffsets, pow_zero, Nat.div_one,
    Nat.mod_eq_of_lt hm]
  rw [RosserBitMoments.enumBits_shift (depth + 3) 1 mask]
  apply List.map_congr_left
  intro d hd
  omega

theorem stepWith_sound (mom : ℕ → ℕ → Moments)
    (hmom : ∀ depth mask len, mask < 2 ^ len →
      len ≤ 2 ^ (depth + 3) →
      mom depth mask = RosserBitMoments.moments
        (RosserBitSieve.windowOffsets (depth + 3) mask 0 len))
    (mask a b v w : ℕ)
    (hcover : ∀ p, Nat.Prime p → a < p → p ≤ b →
      mask.testBit (p - (a + 1)) = true)
    (hv : ((v : ℝ) / scale) ≤ RosserMomentBridge.reciprocalProduct a)
    (h : stepWith mom mask a b v = some w) :
    ((w : ℝ) / scale ≤ RosserMomentBridge.reciprocalProduct b) ∧
      ∀ x : ℝ, (a : ℝ) ≤ x → x ≤ b → RosserBlockCheck.Bound x := by
  let len := b - a
  let depth := depthFor len
  let s := mom depth mask
  let par := parameters a b v
  simp only [stepWith, strictMoments_eq, RosserScan.forceNat_eq] at h
  change (if par.valid && decide (0 < par.intercept ∧
      16384 * s.count < 2 ^ 31 ∧
      par.intercept + par.slope * (32 * ((len + 31) / 32 - 1)) < 2 ^ 31 ∧
      mask < 2 ^ len ∧ len ≤ 2 ^ (depth + 3) ∧
      s.first ≤ s.count * a ∧
      s.count * a ^ 2 - a * s.first + s.second ≤ a ^ 3) &&
      packedCheck mask len (par.intercept - 1) par.slope then
        some (stepFromMoments v a s)
    else none) = some w at h
  let ok := par.valid && decide (0 < par.intercept ∧
      16384 * s.count < 2 ^ 31 ∧
      par.intercept + par.slope * (32 * ((len + 31) / 32 - 1)) < 2 ^ 31 ∧
      mask < 2 ^ len ∧ len ≤ 2 ^ (depth + 3) ∧
      s.first ≤ s.count * a ∧
      s.count * a ^ 2 - a * s.first + s.second ≤ a ^ 3) &&
      packedCheck mask len (par.intercept - 1) par.slope
  change (if ok then some (stepFromMoments v a s) else none) = some w at h
  have hc : ok = true := by
    cases hok : ok with
    | false => simp only [hok, ite_false] at h; cases h
    | true => rfl
  simp only [hc, ite_true] at h
  have hw : stepFromMoments v a s = w := Option.some.inj h
  simp only [ok, Bool.and_eq_true, decide_eq_true_eq] at hc
  rcases hc with ⟨⟨hvalid, hn⟩, hcheck⟩
  obtain ⟨hI, hscount, hrhs0, hmask, hdepth, hfirst, hupper⟩ :=
    hn
  have hmomeq := hmom depth mask len hmask hdepth
  have hlen : len ≤ 2 ^ (depth + 3) := hdepth
  have hcnt : RosserPackedBarrier.candidateCount mask len = s.count := by
    rw [RosserPackedMoments.candidateCount_eq_enumBits_length depth mask len hmask hlen]
    change (RosserBitSieve.enumBits (depth + 3) 1 mask).length =
      (mom depth mask).count
    rw [hmomeq, windowOffsets_eq_enumBits depth mask len hmask]
    rfl
  have hscount' : 16384 * RosserPackedBarrier.candidateCount mask len < 2 ^ 31 := by
    rwa [hcnt]
  have hrhs : (par.intercept - 1) + par.slope *
      (32 * ((len + 31) / 32 - 1)) < 2 ^ 31 := by
    omega
  have hs := RosserFastStep.step_sound a b v mask (depth + 3) s
    hvalid hmask hdepth hcover hmomeq hfirst hupper hI hscount' hrhs hcheck hv
  simpa only [hw] using hs

def step (mask a b v : ℕ) : Option ℕ :=
  stepWith RosserPackedMoments.packedMoments mask a b v

theorem step_sound (mask a b v w : ℕ)
    (hcover : ∀ p, Nat.Prime p → a < p → p ≤ b →
      mask.testBit (p - (a + 1)) = true)
    (hv : ((v : ℝ) / scale) ≤ RosserMomentBridge.reciprocalProduct a)
    (h : step mask a b v = some w) :
    ((w : ℝ) / scale ≤ RosserMomentBridge.reciprocalProduct b) ∧
      ∀ x : ℝ, (a : ℝ) ≤ x → x ≤ b → RosserBlockCheck.Bound x := by
  exact stepWith_sound RosserPackedMoments.packedMoments
    (by
      intro depth mask len hmask hlen
      apply (RosserPackedMoments.packedMoments_sound depth mask
        (hmask.trans_le (Nat.pow_le_pow_right (by omega) hlen))).trans
      rw [windowOffsets_eq_enumBits depth mask len hmask])
    mask a b v w hcover hv h

end RosserFastCompute

-- Source: Solutions/RosserMediumChain.lean
/-! Compose checked prefix blocks using cached sieve masks for segments of at most 2^20 integers. -/

namespace RosserMediumChain

/-- The shared periodic masks cover every segment of this maximum length. -/
def fixedLen : ℕ := 1048576

open RosserScan RosserLogCertificate RosserMomentBridge

structure Checkpoint where
  a : ℕ
  b : ℕ
  initial : ℕ
  final : ℕ

structure Group where
  base : ℕ
  top : ℕ
  initial : ℕ
  final : ℕ
  checkpoints : List Checkpoint

def checkPoints (mask base : ℕ) : List Checkpoint → Bool
  | [] => true
  | c :: cs =>
    (forceNat ((mask >>> (c.a - base)) &&& (2 ^ (c.b - c.a) - 1)) fun window =>
      RosserFastCompute.step window c.a c.b c.initial == some c.final) &&
        checkPoints mask base cs

def checkGroups (ds : List (ℕ × ℕ)) : List Group → Bool
  | [] => true
  | g :: gs =>
    (forceNat (RosserCachedSieve.mask ds g.base g.top) fun mask =>
      checkPoints mask g.base g.checkpoints) && checkGroups ds gs

theorem checkGroups_append (ds : List (ℕ × ℕ)) (xs ys : List Group) :
    checkGroups ds (xs ++ ys) = (checkGroups ds xs && checkGroups ds ys) := by
  induction xs with
  | nil => simp [checkGroups]
  | cons g gs ih =>
    simp only [List.cons_append, checkGroups, ih, Bool.and_assoc]

def allGroups (gs : List Group) : Bool :=
  RosserCachedSieve.withMasks fixedLen RosserSieveData.divisors fun ds =>
    checkGroups ds gs

theorem checkPoints_sound (mask base : ℕ) (cs : List Checkpoint)
    (h : checkPoints mask base cs = true) :
    ∀ c ∈ cs, RosserFastCompute.step
      (mask / 2 ^ (c.a - base) % 2 ^ (c.b - c.a))
      c.a c.b c.initial = some c.final := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [checkPoints, RosserScan.forceNat_eq, Nat.shiftRight_eq_div_pow,
      Nat.and_two_pow_sub_one_eq_mod, Bool.and_eq_true] at h
    obtain ⟨hc, hcs⟩ := h
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact beq_iff_eq.mp hc
    · exact ih hcs d hd

theorem checkGroups_sound (ds : List (ℕ × ℕ)) (gs : List Group)
    (h : checkGroups ds gs = true) :
    ∀ g ∈ gs, ∀ c ∈ g.checkpoints,
      RosserFastCompute.step
        (RosserCachedSieve.mask ds g.base g.top /
          2 ^ (c.a - g.base) % 2 ^ (c.b - c.a))
        c.a c.b c.initial = some c.final := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    simp only [checkGroups, RosserScan.forceNat_eq, Bool.and_eq_true] at h
    obtain ⟨hg, hgs⟩ := h
    intro g' hg' c hc
    rcases List.mem_cons.mp hg' with rfl | hg'
    · exact checkPoints_sound _ _ _ hg c hc
    · exact ih hgs g' hg' c hc

def Linked (a v top w : ℕ) : List Checkpoint → Prop
  | [] => a = top ∧ v = w
  | c :: cs =>
      c.a = a ∧ c.initial = v ∧ a < c.b ∧ c.b ≤ top ∧
        Linked c.b c.final top w cs

def LinkedGroups (a v top : ℕ) : List Group → Prop
  | [] => a = top
  | g :: gs =>
      g.base = a ∧ g.initial = v ∧ g.base < g.top ∧
        g.top - g.base ≤ fixedLen ∧
        Linked g.base g.initial g.top g.final g.checkpoints ∧
        LinkedGroups g.top g.final top gs

def linkedPoints (a v top w : ℕ) : List Checkpoint → Bool
  | [] => decide (a = top ∧ v = w)
  | c :: cs =>
      decide (c.a = a ∧ c.initial = v ∧ a < c.b ∧ c.b ≤ top) &&
        linkedPoints c.b c.final top w cs

def linkedGroups (a v top : ℕ) : List Group → Bool
  | [] => decide (a = top)
  | g :: gs =>
      decide (g.base = a ∧ g.initial = v ∧ g.base < g.top ∧
        g.top - g.base ≤ fixedLen) &&
        linkedPoints g.base g.initial g.top g.final g.checkpoints &&
        linkedGroups g.top g.final top gs

theorem linkedPoints_sound (a v top w : ℕ) (cs : List Checkpoint)
    (h : linkedPoints a v top w cs = true) : Linked a v top w cs := by
  induction cs generalizing a v with
  | nil => simpa only [linkedPoints, decide_eq_true_eq, Linked] using h
  | cons c cs ih =>
    simp only [linkedPoints, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨hc, hrest⟩
    exact ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2,
      ih c.b c.final hrest⟩

theorem linkedGroups_sound (a v top : ℕ) (gs : List Group)
    (h : linkedGroups a v top gs = true) : LinkedGroups a v top gs := by
  induction gs generalizing a v with
  | nil => simpa only [linkedGroups, decide_eq_true_eq, LinkedGroups] using h
  | cons g gs ih =>
    simp only [linkedGroups, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨hg, hp⟩, hrest⟩
    exact ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2,
      linkedPoints_sound _ _ _ _ _ hp, ih g.top g.final hrest⟩

theorem linked_sound (mask base top a v w : ℕ) (cs : List Checkpoint)
    (hcover : RosserScan.Covers base top mask)
    (hbase : base ≤ a)
    (hv : ((v : ℝ) / scale) ≤ reciprocalProduct a)
    (hlinked : Linked a v top w cs)
    (hchecks : ∀ c ∈ cs, RosserFastCompute.step
      (mask / 2 ^ (c.a - base) % 2 ^ (c.b - c.a))
      c.a c.b c.initial = some c.final) :
    ((w : ℝ) / scale ≤ reciprocalProduct top) ∧
      ∀ x : ℝ, (a : ℝ) < x → x ≤ top → RosserBlockCheck.Bound x := by
  induction cs generalizing a v with
  | nil =>
    obtain ⟨rfl, rfl⟩ := hlinked
    refine ⟨hv, ?_⟩
    intro x hax hxt
    linarith
  | cons c cs ih =>
    obtain ⟨hca, hcv, hab, hbt, hrest⟩ := hlinked
    have hstep := hchecks c (by simp)
    have hcover' := RosserPrefixBridge.window_mask_covers base top mask
      c.a c.b hcover (by omega) hbt
    have hrec : ((c.initial : ℝ) / scale) ≤ reciprocalProduct c.a := by
      simpa only [hca, hcv] using hv
    have hs := RosserFastCompute.step_sound _ _ _ _ _ hcover' hrec hstep
    have htail : ∀ d ∈ cs, RosserFastCompute.step
        (mask / 2 ^ (d.a - base) % 2 ^ (d.b - d.a))
        d.a d.b d.initial = some d.final := by
      intro d hd
      exact hchecks d (List.mem_cons_of_mem _ hd)
    have ht := ih c.b c.final (by omega) hs.1 hrest htail
    refine ⟨ht.1, ?_⟩
    intro x hax hxt
    by_cases hxb : x ≤ c.b
    · exact hs.2 x (by exact_mod_cast (show a = c.a by omega) ▸ le_of_lt hax) hxb
    · exact ht.2 x (lt_of_not_ge hxb) hxt

def cachedPairs : List (ℕ × ℕ) :=
  RosserCachedSieve.pairs fixedLen RosserSieveData.divisors

theorem group_sound (g : Group)
    (hshape : g.base < g.top ∧ g.top - g.base ≤ fixedLen)
    (hlink : Linked g.base g.initial g.top g.final g.checkpoints)
    (hcheck : checkPoints
      (RosserCachedSieve.mask cachedPairs g.base g.top)
      g.base g.checkpoints = true)
    (hv : ((g.initial : ℝ) / scale) ≤ reciprocalProduct g.base) :
    ((g.final : ℝ) / scale ≤ reciprocalProduct g.top) ∧
      ∀ x : ℝ, (g.base : ℝ) < x → x ≤ g.top → RosserBlockCheck.Bound x := by
  let m := RosserCachedSieve.mask cachedPairs g.base g.top
  have hcover : RosserScan.Covers g.base g.top m := by
    intro p hp hbp hpt
    exact RosserCachedSieve.mask_prime fixedLen g.base g.top
      RosserSieveData.divisors RosserSieveData.divisors_ge_two
      hshape.1 hshape.2 p hp hbp hpt
  have hs := checkPoints_sound m g.base g.checkpoints hcheck
  exact linked_sound m g.base g.top g.base g.initial g.final
    g.checkpoints hcover (le_refl _) hv hlink hs

theorem groups_sound (gs : List Group) (a v top : ℕ)
    (hv : ((v : ℝ) / scale) ≤ reciprocalProduct a)
    (hlink : LinkedGroups a v top gs)
    (hcheck : checkGroups cachedPairs gs = true) :
    ∀ x : ℝ, (a : ℝ) < x → x ≤ top → RosserBlockCheck.Bound x := by
  induction gs generalizing a v with
  | nil =>
    intro x hax hxt
    change a = top at hlink
    subst top
    linarith
  | cons g gs ih =>
    obtain ⟨hga, hgv, hgt, hwidth, hpoints, hrest⟩ := hlink
    simp only [checkGroups, RosserScan.forceNat_eq, Bool.and_eq_true] at hcheck
    obtain ⟨hgc, hgs⟩ := hcheck
    have hv' : ((g.initial : ℝ) / scale) ≤ reciprocalProduct g.base := by
      simpa only [hga, hgv] using hv
    have hg := group_sound g ⟨hgt, hwidth⟩ hpoints hgc hv'
    have ht := ih g.top g.final hg.1 hrest hgs
    intro x hax hxt
    by_cases hxg : x ≤ g.top
    · apply hg.2 x
      · have : (a : ℝ) = g.base := by exact_mod_cast hga.symm
        linarith only [hax, this]
      · exact hxg
    · exact ht x (lt_of_not_ge hxg) hxt

theorem allGroups_sound (gs : List Group) (a v top : ℕ)
    (hv : ((v : ℝ) / scale) ≤ reciprocalProduct a)
    (hlink : LinkedGroups a v top gs)
    (hcheck : allGroups gs = true) :
    ∀ x : ℝ, (a : ℝ) < x → x ≤ top → RosserBlockCheck.Bound x := by
  simp only [allGroups, RosserCachedSieve.withMasks_eq] at hcheck
  exact groups_sound gs a v top hv hlink hcheck


theorem allGroups_append (xs ys : List Group) :
    allGroups (xs ++ ys) = (allGroups xs && allGroups ys) := by
  simp only [allGroups, RosserCachedSieve.withMasks_eq, checkGroups_append]

theorem allGroups_append_true {xs ys : List Group}
    (hx : allGroups xs = true) (hy : allGroups ys = true) :
    allGroups (xs ++ ys) = true := by
  rw [allGroups_append, hx, hy]
  rfl

#print axioms allGroups_sound

end RosserMediumChain

-- Source: Solutions/RosserMediumSqrtChain.lean
/-! A medium-segment verifier that stops the divisor list at the square-root
cutoff. Its prime-covering proof only uses that selected divisors come from the
original list; no equality with the unfiltered sieve is assumed. -/

namespace RosserMediumSqrtChain

open RosserScan RosserLogCertificate RosserMomentBridge

abbrev Checkpoint := RosserMediumChain.Checkpoint
abbrev Group := RosserMediumChain.Group
abbrev fixedLen := RosserMediumChain.fixedLen
abbrev checkPoints := RosserMediumChain.checkPoints
abbrev Linked := RosserMediumChain.Linked
abbrev LinkedGroups := RosserMediumChain.LinkedGroups
abbrev linkedGroups := RosserMediumChain.linkedGroups
abbrev linkedGroups_sound := RosserMediumChain.linkedGroups_sound

def select (top : ℕ) (ds : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  ds.takeWhile (fun dm => decide (dm.1 * dm.1 ≤ top))

def mask (ds : List (ℕ × ℕ)) (base top : ℕ) : ℕ :=
  RosserCachedSieve.mask (select top ds) base top

theorem select_pairs (len top : ℕ) (ds : List ℕ) :
    select top (RosserCachedSieve.pairs len ds) =
      RosserCachedSieve.pairs len
        (ds.takeWhile (fun d => decide (d * d ≤ top))) := by
  simp only [select, RosserCachedSieve.pairs, List.takeWhile_map,
    Function.comp_def]

theorem mask_prime (len base top : ℕ) (ds : List ℕ)
    (hds : ∀ d ∈ ds, 2 ≤ d) (hbase : base < top)
    (hlen : top - base ≤ len) :
    Covers base top (mask (RosserCachedSieve.pairs len ds) base top) := by
  unfold mask
  rw [select_pairs]
  apply RosserCachedSieve.mask_prime len base top _ _ hbase hlen
  intro d hd
  exact hds d ((List.takeWhile_subset _ ) hd)

def checkGroups (ds : List (ℕ × ℕ)) : List Group → Bool
  | [] => true
  | g :: gs =>
    (forceNat (mask ds g.base g.top) fun mask =>
      checkPoints mask g.base g.checkpoints) && checkGroups ds gs

theorem checkGroups_append (ds : List (ℕ × ℕ)) (xs ys : List Group) :
    checkGroups ds (xs ++ ys) = (checkGroups ds xs && checkGroups ds ys) := by
  induction xs with
  | nil => simp [checkGroups]
  | cons g gs ih =>
    simp only [List.cons_append, checkGroups, ih, Bool.and_assoc]

def allGroups (gs : List Group) : Bool :=
  RosserCachedSieve.withMasks fixedLen RosserSieveData.divisors fun ds =>
    checkGroups ds gs

def cachedPairs : List (ℕ × ℕ) :=
  RosserCachedSieve.pairs fixedLen RosserSieveData.divisors

theorem group_sound (g : Group)
    (hshape : g.base < g.top ∧ g.top - g.base ≤ fixedLen)
    (hlink : Linked g.base g.initial g.top g.final g.checkpoints)
    (hcheck : checkPoints (mask cachedPairs g.base g.top)
      g.base g.checkpoints = true)
    (hv : ((g.initial : ℝ) / scale) ≤ reciprocalProduct g.base) :
    ((g.final : ℝ) / scale ≤ reciprocalProduct g.top) ∧
      ∀ x : ℝ, (g.base : ℝ) < x → x ≤ g.top → RosserBlockCheck.Bound x := by
  have hcover : Covers g.base g.top (mask cachedPairs g.base g.top) :=
    mask_prime fixedLen g.base g.top RosserSieveData.divisors
      RosserSieveData.divisors_ge_two hshape.1 hshape.2
  exact RosserMediumChain.linked_sound _ _ _ _ _ _ _ hcover (le_refl _) hv hlink
    (RosserMediumChain.checkPoints_sound _ _ _ hcheck)

theorem groups_sound (gs : List Group) (a v top : ℕ)
    (hv : ((v : ℝ) / scale) ≤ reciprocalProduct a)
    (hlink : LinkedGroups a v top gs)
    (hcheck : checkGroups cachedPairs gs = true) :
    ∀ x : ℝ, (a : ℝ) < x → x ≤ top → RosserBlockCheck.Bound x := by
  induction gs generalizing a v with
  | nil =>
    intro x hax hxt
    change a = top at hlink
    subst top
    linarith
  | cons g gs ih =>
    obtain ⟨hga, hgv, hgt, hwidth, hpoints, hrest⟩ := hlink
    simp only [checkGroups, RosserScan.forceNat_eq, Bool.and_eq_true] at hcheck
    obtain ⟨hgc, hgs⟩ := hcheck
    have hv' : ((g.initial : ℝ) / scale) ≤ reciprocalProduct g.base := by
      simpa only [hga, hgv] using hv
    have hg := group_sound g ⟨hgt, hwidth⟩ hpoints hgc hv'
    have ht := ih g.top g.final hg.1 hrest hgs
    intro x hax hxt
    by_cases hxg : x ≤ g.top
    · apply hg.2 x
      · have : (a : ℝ) = g.base := by exact_mod_cast hga.symm
        linarith only [hax, this]
      · exact hxg
    · exact ht x (lt_of_not_ge hxg) hxt

theorem allGroups_sound (gs : List Group) (a v top : ℕ)
    (hv : ((v : ℝ) / scale) ≤ reciprocalProduct a)
    (hlink : LinkedGroups a v top gs)
    (hcheck : allGroups gs = true) :
    ∀ x : ℝ, (a : ℝ) < x → x ≤ top → RosserBlockCheck.Bound x := by
  simp only [allGroups, RosserCachedSieve.withMasks_eq] at hcheck
  exact groups_sound gs a v top hv hlink hcheck

theorem allGroups_append (xs ys : List Group) :
    allGroups (xs ++ ys) = (allGroups xs && allGroups ys) := by
  simp only [allGroups, RosserCachedSieve.withMasks_eq, checkGroups_append]

theorem allGroups_append_true {xs ys : List Group}
    (hx : allGroups xs = true) (hy : allGroups ys = true) :
    allGroups (xs ++ ys) = true := by
  rw [allGroups_append, hx, hy]
  rfl

#print axioms allGroups_sound

end RosserMediumSqrtChain

-- Source: Solutions/RosserMediumSqrtCertificates/C00.lean
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RosserMediumSqrtCertificates

def groups00 : List RosserMediumSqrtChain.Group := [
⟨4533, 1053109, 1227903923884082104, 746834254040307770, [
⟨4533, 4698, 1227903923884082104, 1222864545957088161⟩,
⟨4698, 4868, 1222864545957088161, 1218518714552556080⟩,
⟨4868, 5042, 1218518714552556080, 1212634334580089928⟩,
⟨5042, 5221, 1212634334580089928, 1208384508029291058⟩,
⟨5221, 5405, 1208384508029291058, 1204065557340394279⟩,
⟨5405, 5594, 1204065557340394279, 1198378265275869768⟩,
⟨5594, 5787, 1198378265275869768, 1193965581775318888⟩,
⟨5787, 5985, 1193965581775318888, 1189294633353218145⟩,
⟨5985, 6189, 1189294633353218145, 1185000930783120139⟩,
⟨6189, 6398, 1185000930783120139, 1179366987935263115⟩,
⟨6398, 6612, 1179366987935263115, 1175755044942073129⟩,
⟨6612, 6831, 1175755044942073129, 1171393826922972051⟩,
⟨6831, 7056, 1171393826922972051, 1166847394291450639⟩,
⟨7056, 7286, 1166847394291450639, 1163111859378458084⟩,
⟨7286, 7522, 1163111859378458084, 1159506928907307651⟩,
⟨7522, 7764, 1159506928907307651, 1154506146019065388⟩,
⟨7764, 8012, 1154506146019065388, 1151002209228558252⟩,
⟨8012, 8265, 1151002209228558252, 1147192403945651781⟩,
⟨8265, 8524, 1147192403945651781, 1143639366886344855⟩,
⟨8524, 8790, 1143639366886344855, 1139288992373978121⟩,
⟨8790, 9062, 1139288992373978121, 1135339964921612097⟩,
⟨9062, 9340, 1135339964921612097, 1131768965125948094⟩,
⟨9340, 9625, 1131768965125948094, 1127831809354542917⟩,
⟨9625, 9916, 1127831809354542917, 1123913456930961439⟩,
⟨9916, 10213, 1123913456930961439, 1120459774151098500⟩,
⟨10213, 10517, 1120459774151098500, 1116897414514214252⟩,
⟨10517, 10828, 1116897414514214252, 1113864741347132692⟩,
⟨10828, 11146, 1113864741347132692, 1110419575088588302⟩,
⟨11146, 11471, 1110419575088588302, 1107084932459180445⟩,
⟨11471, 11803, 1107084932459180445, 1104139557363206076⟩,
⟨11803, 12142, 1104139557363206076, 1100637177208875015⟩,
⟨12142, 12488, 1100637177208875015, 1097245999127340792⟩,
⟨12488, 12842, 1097245999127340792, 1093696848387977284⟩,
⟨12842, 13203, 1093696848387977284, 1090427417000588725⟩,
⟨13203, 13572, 1090427417000588725, 1087579398031731213⟩,
⟨13572, 13949, 1087579398031731213, 1084186248287059948⟩,
⟨13949, 14333, 1084186248287059948, 1081659164372350798⟩,
⟨14333, 14725, 1081659164372350798, 1078537206898450267⟩,
⟨14725, 15125, 1078537206898450267, 1075430579211598704⟩,
⟨15125, 15533, 1075430579211598704, 1072206365113660122⟩,
⟨15533, 15950, 1072206365113660122, 1069077032291887987⟩,
⟨15950, 16375, 1069077032291887987, 1066368187674476012⟩,
⟨16375, 16809, 1066368187674476012, 1063798885427381497⟩,
⟨16809, 17251, 1063798885427381497, 1060927732285168151⟩,
⟨17251, 17702, 1060927732285168151, 1058077390678887635⟩,
⟨17702, 18162, 1058077390678887635, 1055191108066424444⟩,
⟨18162, 18631, 1055191108066424444, 1052438698102273689⟩,
⟨18631, 19109, 1052438698102273689, 1050210293281258971⟩,
⟨19109, 19596, 1050210293281258971, 1047340184652854070⟩,
⟨19596, 20092, 1047340184652854070, 1044759001488245520⟩,
⟨20092, 20598, 1044759001488245520, 1042141106381588215⟩,
⟨20598, 21113, 1042141106381588215, 1039596431979368181⟩,
⟨21113, 21638, 1039596431979368181, 1036877567173123707⟩,
⟨21638, 22173, 1036877567173123707, 1034137937255070344⟩,
⟨22173, 22718, 1034137937255070344, 1031792862646330633⟩,
⟨22718, 23273, 1031792862646330633, 1029282460654500035⟩,
⟨23273, 23838, 1029282460654500035, 1026752810068538311⟩,
⟨23838, 24413, 1026752810068538311, 1024285644504490563⟩,
⟨24413, 24998, 1024285644504490563, 1022132809469703557⟩,
⟨24998, 25594, 1022132809469703557, 1019872663049441315⟩,
⟨25594, 26200, 1019872663049441315, 1017472507495278140⟩,
⟨26200, 26817, 1017472507495278140, 1015095443410449818⟩,
⟨26817, 27445, 1015095443410449818, 1012925822341728697⟩,
⟨27445, 28084, 1012925822341728697, 1010594289981051599⟩,
⟨28084, 28734, 1010594289981051599, 1008216133255577995⟩,
⟨28734, 29395, 1008216133255577995, 1006033528346600557⟩,
⟨29395, 30068, 1006033528346600557, 1004105365569452229⟩,
⟨30068, 30752, 1004105365569452229, 1001959802093982351⟩,
⟨30752, 31448, 1001959802093982351, 999706084780134538⟩,
⟨31448, 32156, 999706084780134538, 997696181085144187⟩,
⟨32156, 32876, 997696181085144187, 995396494061655100⟩,
⟨32876, 33608, 995396494061655100, 993153611464643517⟩,
⟨33608, 34352, 993153611464643517, 991051173804685991⟩,
⟨34352, 35108, 991051173804685991, 988998321814026361⟩,
⟨35108, 35877, 988998321814026361, 987104771203650104⟩,
⟨35877, 36658, 987104771203650104, 985065492262700722⟩,
⟨36658, 37452, 985065492262700722, 982992979825332631⟩,
⟨37452, 38259, 982992979825332631, 981097892170532470⟩,
⟨38259, 39079, 981097892170532470, 979171349255651376⟩,
⟨39079, 39912, 979171349255651376, 977115442568985694⟩,
⟨39912, 40758, 977115442568985694, 975420602637704030⟩,
⟨40758, 41618, 975420602637704030, 973362043447226364⟩,
⟨41618, 42491, 973362043447226364, 971213095349471549⟩,
⟨42491, 43378, 971213095349471549, 969494312492125406⟩,
⟨43378, 44279, 969494312492125406, 967550648574813279⟩,
⟨44279, 45194, 967550648574813279, 965801058393798888⟩,
⟨45194, 46123, 965801058393798888, 964110190237751640⟩,
⟨46123, 47067, 964110190237751640, 962352341038215444⟩,
⟨47067, 48025, 962352341038215444, 960492148967081889⟩,
⟨48025, 48998, 960492148967081889, 958771509117136810⟩,
⟨48998, 49985, 958771509117136810, 956932178041536748⟩,
⟨49985, 50987, 956932178041536748, 955226721005294701⟩,
⟨50987, 52004, 955226721005294701, 953392172722402000⟩,
⟨52004, 53036, 953392172722402000, 951741767822852651⟩,
⟨53036, 54084, 951741767822852651, 950019307068241262⟩,
⟨54084, 55147, 950019307068241262, 948333508244222241⟩,
⟨55147, 56226, 948333508244222241, 946649459892530828⟩,
⟨56226, 57321, 946649459892530828, 944833915271480032⟩,
⟨57321, 58432, 944833915271480032, 943138041212566894⟩,
⟨58432, 59559, 943138041212566894, 941477496721868644⟩,
⟨59559, 60702, 941477496721868644, 939944104851250670⟩,
⟨60702, 61862, 939944104851250670, 938380903664644635⟩,
⟨61862, 63038, 938380903664644635, 936849366293785332⟩,
⟨63038, 64231, 936849366293785332, 935216457459075561⟩,
⟨64231, 65441, 935216457459075561, 933732676309659039⟩,
⟨65441, 66668, 933732676309659039, 932192500144731685⟩,
⟨66668, 67912, 932192500144731685, 930559276715517552⟩,
⟨67912, 69173, 930559276715517552, 929121234569926382⟩,
⟨69173, 70452, 929121234569926382, 927645492401832747⟩,
⟨70452, 71749, 927645492401832747, 926055124657795018⟩,
⟨71749, 73063, 926055124657795018, 924470705523880388⟩,
⟨73063, 74395, 924470705523880388, 923055738238318126⟩,
⟨74395, 75746, 923055738238318126, 921532591794697475⟩,
⟨75746, 77115, 921532591794697475, 920159157137686813⟩,
⟨77115, 78503, 920159157137686813, 918681340533853868⟩,
⟨78503, 79909, 918681340533853868, 917209831104147325⟩,
⟨79909, 81334, 917209831104147325, 915743730705727219⟩,
⟨81334, 82778, 915743730705727219, 914282891114673638⟩,
⟨82778, 84242, 914282891114673638, 912926453053322996⟩,
⟨84242, 85725, 912926453053322996, 911531141372243907⟩,
⟨85725, 87227, 911531141372243907, 910193532949196514⟩,
⟨87227, 88749, 910193532949196514, 908900605418484830⟩,
⟨88749, 90291, 908900605418484830, 907379030101633102⟩,
⟨90291, 91853, 907379030101633102, 906084877623452711⟩,
⟨91853, 93435, 906084877623452711, 904638627871528704⟩,
⟨93435, 95038, 904638627871528704, 903315049072084962⟩,
⟨95038, 96661, 903315049072084962, 901958427145028755⟩,
⟨96661, 98305, 901958427145028755, 900719024342180942⟩,
⟨98305, 99970, 900719024342180942, 899356970498422668⟩,
⟨99970, 101656, 899356970498422668, 898055806526478005⟩,
⟨101656, 103363, 898055806526478005, 896794380896875975⟩,
⟨103363, 105092, 896794380896875975, 895504691016009095⟩,
⟨105092, 106842, 895504691016009095, 894212839525231787⟩,
⟨106842, 108614, 894212839525231787, 893001802686802739⟩,
⟨108614, 110408, 893001802686802739, 891770661698169552⟩,
⟨110408, 112224, 891770661698169552, 890489593629172667⟩,
⟨112224, 114063, 890489593629172667, 889270334291251630⟩,
⟨114063, 115924, 889270334291251630, 888003448728505380⟩,
⟨115924, 117808, 888003448728505380, 886811583457267063⟩,
⟨117808, 119715, 886811583457267063, 885625008166454028⟩,
⟨119715, 121645, 885625008166454028, 884327314938448567⟩,
⟨121645, 123598, 884327314938448567, 883145601457609678⟩,
⟨123598, 125575, 883145601457609678, 881969507903748238⟩,
⟨125575, 127576, 881969507903748238, 880833954141623350⟩,
⟨127576, 129601, 880833954141623350, 879553817016623129⟩,
⟨129601, 131650, 879553817016623129, 878436822351705259⟩,
⟨131650, 133723, 878436822351705259, 877246050282571623⟩,
⟨133723, 135820, 877246050282571623, 876108085508605686⟩,
⟨135820, 137942, 876108085508605686, 874931013649312452⟩,
⟨137942, 140089, 874931013649312452, 873805064886381931⟩,
⟨140089, 142261, 873805064886381931, 872611322899387754⟩,
⟨142261, 144458, 872611322899387754, 871577303798408462⟩,
⟨144458, 146680, 871577303798408462, 870464376535109829⟩,
⟨146680, 148928, 870464376535109829, 869369585864827404⟩,
⟨148928, 151202, 869369585864827404, 868211393281118308⟩,
⟨151202, 153502, 868211393281118308, 867072167949379817⟩,
⟨153502, 155828, 867072167949379817, 865963152312178833⟩,
⟨155828, 158180, 865963152312178833, 864943524910891428⟩,
⟨158180, 160559, 864943524910891428, 863891213355836505⟩,
⟨160559, 162965, 863891213355836505, 862812973641245520⟩,
⟨162965, 165398, 862812973641245520, 861783386526946175⟩,
⟨165398, 167858, 861783386526946175, 860749574288147796⟩,
⟨167858, 170345, 860749574288147796, 859722200738936844⟩,
⟨170345, 172860, 859722200738936844, 858640761592350803⟩,
⟨172860, 175403, 858640761592350803, 857659933707685183⟩,
⟨175403, 177974, 857659933707685183, 856611857951036674⟩,
⟨177974, 180573, 856611857951036674, 855499366806281598⟩,
⟨180573, 183200, 855499366806281598, 854540778109078800⟩,
⟨183200, 185856, 854540778109078800, 853490272022453031⟩,
⟨185856, 188541, 853490272022453031, 852483059038776505⟩,
⟨188541, 191255, 852483059038776505, 851478021063152500⟩,
⟨191255, 193998, 851478021063152500, 850453222141331312⟩,
⟨193998, 196770, 850453222141331312, 849500634194441366⟩,
⟨196770, 199572, 849500634194441366, 848515169341363308⟩,
⟨199572, 202404, 848515169341363308, 847536384766130863⟩,
⟨202404, 205266, 847536384766130863, 846605607348998289⟩,
⟨205266, 208158, 846605607348998289, 845602819213141471⟩,
⟨208158, 211081, 845602819213141471, 844594917459150029⟩,
⟨211081, 214035, 844594917459150029, 843665671431008378⟩,
⟨214035, 217020, 843665671431008378, 842757956437233139⟩,
⟨217020, 220036, 842757956437233139, 841767675342501017⟩,
⟨220036, 223083, 841767675342501017, 840845085827784152⟩,
⟨223083, 226162, 840845085827784152, 839906007682230322⟩,
⟨226162, 229273, 839906007682230322, 838958841289651212⟩,
⟨229273, 232416, 838958841289651212, 838028730872786027⟩,
⟨232416, 235591, 838028730872786027, 837141118935586210⟩,
⟨235591, 238798, 837141118935586210, 836266471718288469⟩,
⟨238798, 242038, 836266471718288469, 835334912857867843⟩,
⟨242038, 245311, 835334912857867843, 834433874297301099⟩,
⟨245311, 248617, 834433874297301099, 833508678698766218⟩,
⟨248617, 251956, 833508678698766218, 832610041885283869⟩,
⟨251956, 255329, 832610041885283869, 831727650280764304⟩,
⟨255329, 258736, 831727650280764304, 830848072112428523⟩,
⟨258736, 262177, 830848072112428523, 830012742717666614⟩,
⟨262177, 265652, 830012742717666614, 829132632118497014⟩,
⟨265652, 266677, 829132632118497014, 828880337115779467⟩,
⟨266677, 270197, 828880337115779467, 827972804081710338⟩,
⟨270197, 273752, 827972804081710338, 827117580777572612⟩,
⟨273752, 277342, 827117580777572612, 826241573933571448⟩,
⟨277342, 280967, 826241573933571448, 825395687748104013⟩,
⟨280967, 284627, 825395687748104013, 824546771770374756⟩,
⟨284627, 288323, 824546771770374756, 823746783734483779⟩,
⟨288323, 292055, 823746783734483779, 822889835387422419⟩,
⟨292055, 295823, 822889835387422419, 822097845542112810⟩,
⟨295823, 299628, 822097845542112810, 821275242009210911⟩,
⟨299628, 303469, 821275242009210911, 820436844814008426⟩,
⟨303469, 307347, 820436844814008426, 819566870969306825⟩,
⟨307347, 311262, 819566870969306825, 818785615520272317⟩,
⟨311262, 315215, 818785615520272317, 817962617386368437⟩,
⟨315215, 319205, 817962617386368437, 817112157747186726⟩,
⟨319205, 323233, 817112157747186726, 816290802713886857⟩,
⟨323233, 327299, 816290802713886857, 815485562817805415⟩,
⟨327299, 331403, 815485562817805415, 814661385978522073⟩,
⟨331403, 335546, 814661385978522073, 813875150375172267⟩,
⟨335546, 339728, 813875150375172267, 813092012546485789⟩,
⟨339728, 343949, 813092012546485789, 812302728485046176⟩,
⟨343949, 348209, 812302728485046176, 811516812577618019⟩,
⟨348209, 352509, 811516812577618019, 810715848183206826⟩,
⟨352509, 356848, 810715848183206826, 809957202650158801⟩,
⟨356848, 361228, 809957202650158801, 809212897419353525⟩,
⟨361228, 365648, 809212897419353525, 808418435382034822⟩,
⟨365648, 370108, 808418435382034822, 807682480323217159⟩,
⟨370108, 374609, 807682480323217159, 806956179604837498⟩,
⟨374609, 379151, 806956179604837498, 806179145065825804⟩,
⟨379151, 383734, 806179145065825804, 805439737785620862⟩,
⟨383734, 388359, 805439737785620862, 804697178901836712⟩,
⟨388359, 393025, 804697178901836712, 803914954960278676⟩,
⟨393025, 397733, 803914954960278676, 803179125713143489⟩,
⟨397733, 402484, 803179125713143489, 802458652263255658⟩,
⟨402484, 407277, 802458652263255658, 801755290791791478⟩,
⟨407277, 412113, 801755290791791478, 800994387786684848⟩,
⟨412113, 416992, 800994387786684848, 800285591944922958⟩,
⟨416992, 421914, 800285591944922958, 799549374460952499⟩,
⟨421914, 426880, 799549374460952499, 798833696228917913⟩,
⟨426880, 431890, 798833696228917913, 798099220489603304⟩,
⟨431890, 436944, 798099220489603304, 797355397544097747⟩,
⟨436944, 442042, 797355397544097747, 796657264356460174⟩,
⟨442042, 447184, 796657264356460174, 795946025977707703⟩,
⟨447184, 452371, 795946025977707703, 795234992616706968⟩,
⟨452371, 457603, 795234992616706968, 794555502312127126⟩,
⟨457603, 462881, 794555502312127126, 793894573954973923⟩,
⟨462881, 468204, 793894573954973923, 793183813553466934⟩,
⟨468204, 473573, 793183813553466934, 792476657000421059⟩,
⟨473573, 478988, 792476657000421059, 791769816229470029⟩,
⟨478988, 484450, 791769816229470029, 791081445166427736⟩,
⟨484450, 489958, 791081445166427736, 790414551174492783⟩,
⟨489958, 495513, 790414551174492783, 789725115693436668⟩,
⟨495513, 501115, 789725115693436668, 789036055227222943⟩,
⟨501115, 506765, 789036055227222943, 788375664433452830⟩,
⟨506765, 512462, 788375664433452830, 787727663882217972⟩,
⟨512462, 518207, 787727663882217972, 787029426995780286⟩,
⟨518207, 524001, 787029426995780286, 786365155000293291⟩,
⟨524001, 528821, 786365155000293291, 785814078976454956⟩,
⟨528821, 534704, 785814078976454956, 785153782113333152⟩,
⟨534704, 540635, 785153782113333152, 784510077270320534⟩,
⟨540635, 546616, 784510077270320534, 783872438285568555⟩,
⟨546616, 552646, 783872438285568555, 783222340291132415⟩,
⟨552646, 558726, 783222340291132415, 782581252464007495⟩,
⟨558726, 564856, 782581252464007495, 781943442397166145⟩,
⟨564856, 571037, 781943442397166145, 781289799231735313⟩,
⟨571037, 577268, 781289799231735313, 780650506735845070⟩,
⟨577268, 583550, 780650506735845070, 780003845843801666⟩,
⟨583550, 589883, 780003845843801666, 779356688406813912⟩,
⟨589883, 596268, 779356688406813912, 778728894549917807⟩,
⟨596268, 602705, 778728894549917807, 778104368294189608⟩,
⟨602705, 609194, 778104368294189608, 777476693701933454⟩,
⟨609194, 615735, 777476693701933454, 776854884951022687⟩,
⟨615735, 622329, 776854884951022687, 776226310530416509⟩,
⟨622329, 628976, 776226310530416509, 775632214090632244⟩,
⟨628976, 635676, 775632214090632244, 775013058295931819⟩,
⟨635676, 642429, 775013058295931819, 774427500024323179⟩,
⟨642429, 649236, 774427500024323179, 773813806874725917⟩,
⟨649236, 656097, 773813806874725917, 773208165400586409⟩,
⟨656097, 663012, 773208165400586409, 772601147144538646⟩,
⟨663012, 669982, 772601147144538646, 772004341633186330⟩,
⟨669982, 677007, 772004341633186330, 771400474599902298⟩,
⟨677007, 684087, 771400474599902298, 770801078129357362⟩,
⟨684087, 691222, 770801078129357362, 770209397993125461⟩,
⟨691222, 698413, 770209397993125461, 769606572983795187⟩,
⟨698413, 705660, 769606572983795187, 769019262836672291⟩,
⟨705660, 712964, 769019262836672291, 768415596903153373⟩,
⟨712964, 720324, 768415596903153373, 767849673103184414⟩,
⟨720324, 727741, 767849673103184414, 767253865931008423⟩,
⟨727741, 735215, 767253865931008423, 766670929642073151⟩,
⟨735215, 742747, 766670929642073151, 766097413251295089⟩,
⟨742747, 750337, 766097413251295089, 765549686714735760⟩,
⟨750337, 757985, 765549686714735760, 764983390983399015⟩,
⟨757985, 765691, 764983390983399015, 764390157526588506⟩,
⟨765691, 773456, 764390157526588506, 763817221256814868⟩,
⟨773456, 781280, 763817221256814868, 763255400879690745⟩,
⟨781280, 789163, 763255400879690745, 762680174436018599⟩,
⟨789163, 790965, 762680174436018599, 762556627769161931⟩,
⟨790965, 798921, 762556627769161931, 761986055946053159⟩,
⟨798921, 806937, 761986055946053159, 761430121425506275⟩,
⟨806937, 815013, 761430121425506275, 760875432377180492⟩,
⟨815013, 823150, 760875432377180492, 760315527503632305⟩,
⟨823150, 831348, 760315527503632305, 759760534012061836⟩,
⟨831348, 839607, 759760534012061836, 759215036791798472⟩,
⟨839607, 847927, 759215036791798472, 758669037969195248⟩,
⟨847927, 856309, 758669037969195248, 758129672250103643⟩,
⟨856309, 864753, 758129672250103643, 757577481959520281⟩,
⟨864753, 873260, 757577481959520281, 757032760122763022⟩,
⟨873260, 881829, 757032760122763022, 756483441271228839⟩,
⟨881829, 890461, 756483441271228839, 755950919857552621⟩,
⟨890461, 899157, 755950919857552621, 755414619162384314⟩,
⟨899157, 907916, 755414619162384314, 754880632838054576⟩,
⟨907916, 916739, 754880632838054576, 754356992926494670⟩,
⟨916739, 925626, 754356992926494670, 753809379277776664⟩,
⟨925626, 934578, 753809379277776664, 753290073811435943⟩,
⟨934578, 943595, 753290073811435943, 752763267829025119⟩,
⟨943595, 952677, 752763267829025119, 752252167223736259⟩,
⟨952677, 961824, 752252167223736259, 751736085896773745⟩,
⟨961824, 971037, 751736085896773745, 751215893720377037⟩,
⟨971037, 980316, 751215893720377037, 750710137075938254⟩,
⟨980316, 989662, 750710137075938254, 750206488877008244⟩,
⟨989662, 999075, 750206488877008244, 749684592220766375⟩,
⟨999075, 1008555, 749684592220766375, 749160528339477307⟩,
⟨1008555, 1018102, 749160528339477307, 748649822947636555⟩,
⟨1018102, 1027717, 748649822947636555, 748134737273102458⟩,
⟨1027717, 1037400, 748134737273102458, 747634238582211966⟩,
⟨1037400, 1047151, 747634238582211966, 747134443024039724⟩,
⟨1047151, 1053109, 747134443024039724, 746834254040307770⟩
]⟩
]

theorem c00 : RosserMediumSqrtChain.allGroups groups00 = true :=
  by decide +kernel

end RosserMediumSqrtCertificates

-- Source: Solutions/RosserMediumSqrtCertificates/C01.lean
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RosserMediumSqrtCertificates

def groups01 : List RosserMediumSqrtChain.Group := [
⟨1053109, 2101685, 746834254040307770, 711387179728933604, [
⟨1053109, 1062971, 746834254040307770, 746351569007585899⟩,
⟨1062971, 1072902, 746351569007585899, 745848501264914475⟩,
⟨1072902, 1082902, 745848501264914475, 745340080100615062⟩,
⟨1082902, 1092972, 745340080100615062, 744849728485022296⟩,
⟨1092972, 1103112, 744849728485022296, 744345188243651623⟩,
⟨1103112, 1113323, 744345188243651623, 743835599047695396⟩,
⟨1113323, 1123605, 743835599047695396, 743359560232283192⟩,
⟨1123605, 1133958, 743359560232283192, 742863193352580701⟩,
⟨1133958, 1144382, 742863193352580701, 742385328841194415⟩,
⟨1144382, 1154878, 742385328841194415, 741904389522653538⟩,
⟨1154878, 1165446, 741904389522653538, 741397458138638471⟩,
⟨1165446, 1176087, 741397458138638471, 740920141575609355⟩,
⟨1176087, 1186800, 740920141575609355, 740426100016868273⟩,
⟨1186800, 1197586, 740426100016868273, 739941807138597415⟩,
⟨1197586, 1208446, 739941807138597415, 739484930958675169⟩,
⟨1208446, 1219380, 739484930958675169, 739003831393694399⟩,
⟨1219380, 1230388, 739003831393694399, 738533385863152295⟩,
⟨1230388, 1241470, 738533385863152295, 738074630784327374⟩,
⟨1241470, 1252627, 738074630784327374, 737603647888767294⟩,
⟨1252627, 1263859, 737603647888767294, 737127785981549072⟩,
⟨1263859, 1275167, 737127785981549072, 736658731396879406⟩,
⟨1275167, 1286550, 736658731396879406, 736193599116489594⟩,
⟨1286550, 1298010, 736193599116489594, 735729426824621109⟩,
⟨1298010, 1309546, 735729426824621109, 735275857050445625⟩,
⟨1309546, 1315253, 735275857050445625, 735049530228201076⟩,
⟨1315253, 1326904, 735049530228201076, 734580639020853645⟩,
⟨1326904, 1338632, 734580639020853645, 734134343504370809⟩,
⟨1338632, 1350438, 734134343504370809, 733682866967949108⟩,
⟨1350438, 1362322, 733682866967949108, 733225373322694487⟩,
⟨1362322, 1374284, 733225373322694487, 732775358837470374⟩,
⟨1374284, 1386325, 732775358837470374, 732312556833999757⟩,
⟨1386325, 1398445, 732312556833999757, 731854664026808353⟩,
⟨1398445, 1410644, 731854664026808353, 731414485908037060⟩,
⟨1410644, 1422923, 731414485908037060, 730983000768518885⟩,
⟨1422923, 1435282, 730983000768518885, 730517692153537743⟩,
⟨1435282, 1447722, 730517692153537743, 730072387806148525⟩,
⟨1447722, 1460242, 730072387806148525, 729631160456650267⟩,
⟨1460242, 1472843, 729631160456650267, 729190467201835406⟩,
⟨1472843, 1485526, 729190467201835406, 728747913285918868⟩,
⟨1485526, 1498291, 728747913285918868, 728305476104238957⟩,
⟨1498291, 1511138, 728305476104238957, 727855975727419486⟩,
⟨1511138, 1524068, 727855975727419486, 727428757074112434⟩,
⟨1524068, 1537080, 727428757074112434, 727002093821092445⟩,
⟨1537080, 1550175, 727002093821092445, 726571765584505214⟩,
⟨1550175, 1563354, 726571765584505214, 726142958942055825⟩,
⟨1563354, 1576617, 726142958942055825, 725712472266787916⟩,
⟨1576617, 1577397, 725712472266787916, 725686242340694913⟩,
⟨1577397, 1590749, 725686242340694913, 725265373731840417⟩,
⟨1590749, 1604186, 725265373731840417, 724834707872122075⟩,
⟨1604186, 1617708, 724834707872122075, 724419969752196848⟩,
⟨1617708, 1631316, 724419969752196848, 723987984382357445⟩,
⟨1631316, 1645009, 723987984382357445, 723569117762665013⟩,
⟨1645009, 1658788, 723569117762665013, 723147420134357887⟩,
⟨1658788, 1672654, 723147420134357887, 722726004630782333⟩,
⟨1672654, 1686607, 722726004630782333, 722303999010939999⟩,
⟨1686607, 1700647, 722303999010939999, 721886192340934630⟩,
⟨1700647, 1714774, 721886192340934630, 721474561973486536⟩,
⟨1714774, 1728989, 721474561973486536, 721063212929946340⟩,
⟨1728989, 1743293, 721063212929946340, 720655895026531535⟩,
⟨1743293, 1757685, 720655895026531535, 720236481114075642⟩,
⟨1757685, 1772166, 720236481114075642, 719839945395738358⟩,
⟨1772166, 1786737, 719839945395738358, 719422572782842934⟩,
⟨1786737, 1801398, 719422572782842934, 719012077331450988⟩,
⟨1801398, 1816149, 719012077331450988, 718601175642631297⟩,
⟨1816149, 1830990, 718601175642631297, 718193472584569174⟩,
⟨1830990, 1839541, 718193472584569174, 717970824698156482⟩,
⟨1839541, 1854525, 717970824698156482, 717562785515978820⟩,
⟨1854525, 1869601, 717562785515978820, 717149020863360201⟩,
⟨1869601, 1884769, 717149020863360201, 716751817665766292⟩,
⟨1884769, 1900029, 716751817665766292, 716350804544057772⟩,
⟨1900029, 1915381, 716350804544057772, 715950643513832001⟩,
⟨1915381, 1930826, 715950643513832001, 715546460774942434⟩,
⟨1930826, 1946365, 715546460774942434, 715151272718636564⟩,
⟨1946365, 1961997, 715151272718636564, 714756876586213686⟩,
⟨1961997, 1977723, 714756876586213686, 714379616647844936⟩,
⟨1977723, 1993544, 714379616647844936, 713983244515253026⟩,
⟨1993544, 2009460, 713983244515253026, 713582397449348505⟩,
⟨2009460, 2025471, 713582397449348505, 713193058765066959⟩,
⟨2025471, 2041578, 713193058765066959, 712802439616943041⟩,
⟨2041578, 2057781, 712802439616943041, 712417914069908950⟩,
⟨2057781, 2074080, 712417914069908950, 712031088139498643⟩,
⟨2074080, 2090475, 712031088139498643, 711646171102790687⟩,
⟨2090475, 2101685, 711646171102790687, 711387179728933604⟩
]⟩
]

theorem c01 : RosserMediumSqrtChain.allGroups groups01 = true :=
  by decide +kernel

end RosserMediumSqrtCertificates

-- Source: Solutions/RosserMediumSqrtCertificates/C02.lean
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RosserMediumSqrtCertificates

def groups02 : List RosserMediumSqrtChain.Group := [
⟨2101685, 3150261, 711387179728933604, 692159501558396181, [
⟨2101685, 2118244, 711387179728933604, 711000234249897560⟩,
⟨2118244, 2134901, 711000234249897560, 710623868398455933⟩,
⟨2134901, 2151656, 710623868398455933, 710238685674277044⟩,
⟨2151656, 2168509, 710238685674277044, 709857680844155852⟩,
⟨2168509, 2185461, 709857680844155852, 709479193389082228⟩,
⟨2185461, 2202513, 709479193389082228, 709107711166380078⟩,
⟨2202513, 2219664, 709107711166380078, 708733516811587403⟩,
⟨2219664, 2236915, 708733516811587403, 708353227656122526⟩,
⟨2236915, 2254267, 708353227656122526, 707985208677132535⟩,
⟨2254267, 2271720, 707985208677132535, 707599565282763320⟩,
⟨2271720, 2289274, 707599565282763320, 707232891752356237⟩,
⟨2289274, 2306929, 707232891752356237, 706864603574665265⟩,
⟨2306929, 2324686, 706864603574665265, 706499617876901336⟩,
⟨2324686, 2342546, 706499617876901336, 706131577731443600⟩,
⟨2342546, 2360509, 706131577731443600, 705768642226780520⟩,
⟨2360509, 2363829, 705768642226780520, 705701420640337526⟩,
⟨2363829, 2381914, 705701420640337526, 705333622819694622⟩,
⟨2381914, 2400103, 705333622819694622, 704964982370944311⟩,
⟨2400103, 2418396, 704964982370944311, 704603722626215472⟩,
⟨2418396, 2436793, 704603722626215472, 704243615383162575⟩,
⟨2436793, 2455295, 704243615383162575, 703881814598594509⟩,
⟨2455295, 2473902, 703881814598594509, 703521752164664176⟩,
⟨2473902, 2492615, 703521752164664176, 703162898651021431⟩,
⟨2492615, 2511434, 703162898651021431, 702803546075980634⟩,
⟨2511434, 2530360, 702803546075980634, 702439836313375775⟩,
⟨2530360, 2549392, 702439836313375775, 702088971569938284⟩,
⟨2549392, 2568532, 702088971569938284, 701732944960057118⟩,
⟨2568532, 2587779, 701732944960057118, 701372118948445762⟩,
⟨2587779, 2607135, 701372118948445762, 701022510236000246⟩,
⟨2607135, 2625973, 701022510236000246, 700680457305019109⟩,
⟨2625973, 2645542, 700680457305019109, 700326985927559810⟩,
⟨2645542, 2665221, 700326985927559810, 699969182738902167⟩,
⟨2665221, 2685009, 699969182738902167, 699626771952737522⟩,
⟨2685009, 2704907, 699626771952737522, 699275601314442223⟩,
⟨2704907, 2724916, 699275601314442223, 698923577028382324⟩,
⟨2724916, 2745036, 698923577028382324, 698582771417783847⟩,
⟨2745036, 2765267, 698582771417783847, 698238537035859097⟩,
⟨2765267, 2785610, 698238537035859097, 697893959507998854⟩,
⟨2785610, 2806065, 697893959507998854, 697549337639732838⟩,
⟨2806065, 2826633, 697549337639732838, 697197956147630877⟩,
⟨2826633, 2847313, 697197956147630877, 696852998241443425⟩,
⟨2847313, 2868107, 696852998241443425, 696511451733582145⟩,
⟨2868107, 2888117, 696511451733582145, 696192336679748187⟩,
⟨2888117, 2909134, 696192336679748187, 695854492377793130⟩,
⟨2909134, 2930266, 695854492377793130, 695517810924473718⟩,
⟨2930266, 2951512, 695517810924473718, 695183243339208128⟩,
⟨2951512, 2972874, 695183243339208128, 694848430441649973⟩,
⟨2972874, 2994352, 694848430441649973, 694512910549512825⟩,
⟨2994352, 3015946, 694512910549512825, 694174410908934406⟩,
⟨3015946, 3037657, 694174410908934406, 693848818414987075⟩,
⟨3037657, 3059485, 693848818414987075, 693516600324303128⟩,
⟨3059485, 3081430, 693516600324303128, 693181062924796741⟩,
⟨3081430, 3103493, 693181062924796741, 692851407397077358⟩,
⟨3103493, 3125675, 692851407397077358, 692520245360551277⟩,
⟨3125675, 3147976, 692520245360551277, 692193350863240859⟩,
⟨3147976, 3150261, 692193350863240859, 692159501558396181⟩
]⟩,
⟨3150261, 4198837, 692159501558396181, 679116762961672288, [
⟨3150261, 3172693, 692159501558396181, 691826578894761963⟩,
⟨3172693, 3195245, 691826578894761963, 691497913424194579⟩,
⟨3195245, 3217917, 691497913424194579, 691163300734312696⟩,
⟨3217917, 3240709, 691163300734312696, 690833999525618383⟩,
⟨3240709, 3263623, 690833999525618383, 690512902009728978⟩,
⟨3263623, 3286658, 690512902009728978, 690189130219056260⟩,
⟨3286658, 3309815, 690189130219056260, 689867365115398263⟩,
⟨3309815, 3333094, 689867365115398263, 689548196533110966⟩,
⟨3333094, 3356496, 689548196533110966, 689229542514562595⟩,
⟨3356496, 3380021, 689229542514562595, 688909393410150593⟩,
⟨3380021, 3403669, 688909393410150593, 688586941460288656⟩,
⟨3403669, 3412405, 688586941460288656, 688467140403855396⟩,
⟨3412405, 3436223, 688467140403855396, 688150155865235073⟩,
⟨3436223, 3460166, 688150155865235073, 687831294266566833⟩,
⟨3460166, 3484234, 687831294266566833, 687522923881815346⟩,
⟨3484234, 3508427, 687522923881815346, 687213681463257123⟩,
⟨3508427, 3532746, 687213681463257123, 686902795814348338⟩,
⟨3532746, 3557191, 686902795814348338, 686592648541422595⟩,
⟨3557191, 3581763, 686592648541422595, 686281101561204532⟩,
⟨3581763, 3606462, 686281101561204532, 685965731906929185⟩,
⟨3606462, 3631289, 685965731906929185, 685643747508489876⟩,
⟨3631289, 3656244, 685643747508489876, 685342924310926013⟩,
⟨3656244, 3674549, 685342924310926013, 685114661892232144⟩,
⟨3674549, 3699727, 685114661892232144, 684798293536892253⟩,
⟨3699727, 3725034, 684798293536892253, 684489211571763969⟩,
⟨3725034, 3750471, 684489211571763969, 684179416392375764⟩,
⟨3750471, 3776038, 684179416392375764, 683878046095377871⟩,
⟨3776038, 3801735, 683878046095377871, 683572355678194519⟩,
⟨3801735, 3827563, 683572355678194519, 683264559366045718⟩,
⟨3827563, 3853523, 683264559366045718, 682958792134058659⟩,
⟨3853523, 3879615, 682958792134058659, 682658575811013991⟩,
⟨3879615, 3905839, 682658575811013991, 682354891218379381⟩,
⟨3905839, 3932196, 682354891218379381, 682047300040118931⟩,
⟨3932196, 3936693, 682047300040118931, 681998762788944554⟩,
⟨3936693, 3963206, 681998762788944554, 681698378699728890⟩,
⟨3963206, 3989853, 681698378699728890, 681401172614657729⟩,
⟨3989853, 4016634, 681401172614657729, 681102180820261168⟩,
⟨4016634, 4043550, 681102180820261168, 680797206447961563⟩,
⟨4043550, 4070601, 680797206447961563, 680500752247085385⟩,
⟨4070601, 4097788, 680500752247085385, 680199569928972454⟩,
⟨4097788, 4125111, 680199569928972454, 679907624198557787⟩,
⟨4125111, 4152570, 679907624198557787, 679614300418350430⟩,
⟨4152570, 4180166, 679614300418350430, 679317316167851028⟩,
⟨4180166, 4198837, 679317316167851028, 679116762961672288⟩
]⟩
]

theorem c02 : RosserMediumSqrtChain.allGroups groups02 = true :=
  by decide +kernel

end RosserMediumSqrtCertificates

-- Source: Solutions/RosserMediumSqrtCertificates/C03.lean
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RosserMediumSqrtCertificates

def groups03 : List RosserMediumSqrtChain.Group := [
⟨4198837, 5247413, 679116762961672288, 669330067939499994, [
⟨4198837, 4226664, 679116762961672288, 678820207510398227⟩,
⟨4226664, 4254629, 678820207510398227, 678528149738622389⟩,
⟨4254629, 4282732, 678528149738622389, 678239076115177399⟩,
⟨4282732, 4310974, 678239076115177399, 677952179796496791⟩,
⟨4310974, 4339356, 677952179796496791, 677660534874292182⟩,
⟨4339356, 4367878, 677660534874292182, 677375433277339364⟩,
⟨4367878, 4396540, 677375433277339364, 677084575014164387⟩,
⟨4396540, 4425343, 677084575014164387, 676793456497151637⟩,
⟨4425343, 4454288, 676793456497151637, 676498702645375709⟩,
⟨4454288, 4460981, 676498702645375709, 676431475864370834⟩,
⟨4460981, 4490101, 676431475864370834, 676140753841739784⟩,
⟨4490101, 4519363, 676140753841739784, 675858777709929698⟩,
⟨4519363, 4548768, 675858777709929698, 675576065007681746⟩,
⟨4548768, 4578316, 675576065007681746, 675289078199152276⟩,
⟨4578316, 4608008, 675289078199152276, 675003917511366736⟩,
⟨4608008, 4637844, 675003917511366736, 674720271266918526⟩,
⟨4637844, 4667825, 674720271266918526, 674441034077476621⟩,
⟨4667825, 4697951, 674441034077476621, 674152185774999539⟩,
⟨4697951, 4723125, 674152185774999539, 673918666457202973⟩,
⟨4723125, 4753519, 673918666457202973, 673640800543963898⟩,
⟨4753519, 4784059, 673640800543963898, 673360028136524692⟩,
⟨4784059, 4814746, 673360028136524692, 673081871951750991⟩,
⟨4814746, 4845581, 673081871951750991, 672803086943756383⟩,
⟨4845581, 4876564, 672803086943756383, 672524109513070700⟩,
⟨4876564, 4907695, 672524109513070700, 672238638931547763⟩,
⟨4907695, 4938975, 672238638931547763, 671962748019109538⟩,
⟨4938975, 4970405, 671962748019109538, 671683290465292949⟩,
⟨4970405, 4985269, 671683290465292949, 671551742956075629⟩,
⟨4985269, 5016919, 671551742956075629, 671277456496580946⟩,
⟨5016919, 5048720, 671277456496580946, 671005276199741985⟩,
⟨5048720, 5080672, 671005276199741985, 670729492595303979⟩,
⟨5080672, 5112776, 670729492595303979, 670458050706669687⟩,
⟨5112776, 5145032, 670458050706669687, 670182026178493246⟩,
⟨5145032, 5177440, 670182026178493246, 669914201195580367⟩,
⟨5177440, 5210001, 669914201195580367, 669642100667801257⟩,
⟨5210001, 5242716, 669642100667801257, 669371032955749889⟩,
⟨5242716, 5247413, 669371032955749889, 669330067939499994⟩
]⟩,
⟨5247413, 6295989, 669330067939499994, 661549122857649016, [
⟨5247413, 5280304, 669330067939499994, 669058894637148742⟩,
⟨5280304, 5313349, 669058894637148742, 668790785060544344⟩,
⟨5313349, 5346549, 668790785060544344, 668519185317139341⟩,
⟨5346549, 5379905, 668519185317139341, 668252623468030893⟩,
⟨5379905, 5413417, 668252623468030893, 667986318802241001⟩,
⟨5413417, 5447085, 667986318802241001, 667719554110329638⟩,
⟨5447085, 5480910, 667719554110329638, 667452828300874250⟩,
⟨5480910, 5509557, 667452828300874250, 667228166259314888⟩,
⟨5509557, 5543673, 667228166259314888, 666966841088109271⟩,
⟨5543673, 5577947, 666966841088109271, 666703864274418073⟩,
⟨5577947, 5612380, 666703864274418073, 666439269506518606⟩,
⟨5612380, 5646972, 666439269506518606, 666180302404560248⟩,
⟨5646972, 5681724, 666180302404560248, 665919843631511674⟩,
⟨5681724, 5716636, 665919843631511674, 665653254882095820⟩,
⟨5716636, 5751709, 665653254882095820, 665391417138053452⟩,
⟨5751709, 5771701, 665391417138053452, 665246266889626560⟩,
⟨5771701, 5807027, 665246266889626560, 664986972592813823⟩,
⟨5807027, 5842515, 664986972592813823, 664729575546365497⟩,
⟨5842515, 5878165, 664729575546365497, 664469190462663428⟩,
⟨5878165, 5913978, 664469190462663428, 664204855398193153⟩,
⟨5913978, 5949955, 664204855398193153, 663944679137828714⟩,
⟨5949955, 5986096, 663944679137828714, 663689519061932000⟩,
⟨5986096, 6022402, 663689519061932000, 663431906651057409⟩,
⟨6022402, 6033845, 663431906651057409, 663349036750420313⟩,
⟨6033845, 6070367, 663349036750420313, 663097542903962453⟩,
⟨6070367, 6107055, 663097542903962453, 662840465316443946⟩,
⟨6107055, 6143909, 662840465316443946, 662585893769099455⟩,
⟨6143909, 6180930, 662585893769099455, 662329613734830268⟩,
⟨6180930, 6218118, 662329613734830268, 662079026512745223⟩,
⟨6218118, 6255474, 662079026512745223, 661826421593278856⟩,
⟨6255474, 6292998, 661826421593278856, 661570037958656138⟩,
⟨6292998, 6295989, 661570037958656138, 661549122857649016⟩
]⟩,
⟨6295989, 7344565, 661549122857649016, 655102158259008508, [
⟨6295989, 6333695, 661549122857649016, 661293235271643109⟩,
⟨6333695, 6371570, 661293235271643109, 661046150085727730⟩,
⟨6371570, 6409615, 661046150085727730, 660797323828301679⟩,
⟨6409615, 6447830, 660797323828301679, 660549853400036559⟩,
⟨6447830, 6486216, 660549853400036559, 660299445450357534⟩,
⟨6486216, 6524773, 660299445450357534, 660049196388447511⟩,
⟨6524773, 6558133, 660049196388447511, 659836021265356874⟩,
⟨6558133, 6597011, 659836021265356874, 659584671010438148⟩,
⟨6597011, 6636061, 659584671010438148, 659336489114925506⟩,
⟨6636061, 6675285, 659336489114925506, 659090858235899802⟩,
⟨6675285, 6714682, 659090858235899802, 658843125839654428⟩,
⟨6714682, 6754254, 658843125839654428, 658595950512511671⟩,
⟨6754254, 6794000, 658595950512511671, 658352639045304066⟩,
⟨6794000, 6820277, 658352639045304066, 658188245550374848⟩,
⟨6820277, 6860315, 658188245550374848, 657942641958049428⟩,
⟨6860315, 6900529, 657942641958049428, 657696253896023542⟩,
⟨6900529, 6940919, 657696253896023542, 657452255329067961⟩,
⟨6940919, 6981486, 657452255329067961, 657207586898902617⟩,
⟨6981486, 7022231, 657207586898902617, 656965656340709244⟩,
⟨7022231, 7063154, 656965656340709244, 656721101712271037⟩,
⟨7063154, 7082421, 656721101712271037, 656607276009500869⟩,
⟨7082421, 7123607, 656607276009500869, 656364567693339875⟩,
⟨7123607, 7164973, 656364567693339875, 656126667051516911⟩,
⟨7164973, 7206519, 656126667051516911, 655887754123215946⟩,
⟨7206519, 7248245, 655887754123215946, 655647311515079270⟩,
⟨7248245, 7290152, 655647311515079270, 655407347221250480⟩,
⟨7290152, 7332241, 655407347221250480, 655169472705783395⟩,
⟨7332241, 7344565, 655169472705783395, 655102158259008508⟩
]⟩,
⟨7344565, 8393141, 655102158259008508, 649622041016209911, [
⟨7344565, 7386889, 655102158259008508, 654861974240292090⟩,
⟨7386889, 7429396, 654861974240292090, 654625822942394167⟩,
⟨7429396, 7472086, 654625822942394167, 654391093730019713⟩,
⟨7472086, 7514960, 654391093730019713, 654155606178499060⟩,
⟨7514960, 7558019, 654155606178499060, 653917652449585856⟩,
⟨7558019, 7601263, 653917652449585856, 653683212807005359⟩,
⟨7601263, 7606709, 653683212807005359, 653652438024113423⟩,
⟨7606709, 7650161, 653652438024113423, 653418043106755796⟩,
⟨7650161, 7693799, 653418043106755796, 653181998380208216⟩,
⟨7693799, 7737624, 653181998380208216, 652950163413433171⟩,
⟨7737624, 7781636, 652950163413433171, 652717372966922432⟩,
⟨7781636, 7825836, 652717372966922432, 652485565209569691⟩,
⟨7825836, 7868853, 652485565209569691, 652258695618357748⟩,
⟨7868853, 7913424, 652258695618357748, 652025805862889809⟩,
⟨7913424, 7958184, 652025805862889809, 651795459457850956⟩,
⟨7958184, 8003134, 651795459457850956, 651564447189214804⟩,
⟨8003134, 8048274, 651564447189214804, 651335547096411072⟩,
⟨8048274, 8093605, 651335547096411072, 651107113800766087⟩,
⟨8093605, 8130997, 651107113800766087, 650917807577041205⟩,
⟨8130997, 8176677, 650917807577041205, 650690890898085044⟩,
⟨8176677, 8222549, 650690890898085044, 650459207482973259⟩,
⟨8222549, 8268614, 650459207482973259, 650232996413482241⟩,
⟨8268614, 8314872, 650232996413482241, 650003578133384853⟩,
⟨8314872, 8361324, 650003578133384853, 649775908868761752⟩,
⟨8361324, 8393141, 649775908868761752, 649622041016209911⟩
]⟩
]

theorem c03 : RosserMediumSqrtChain.allGroups groups03 = true :=
  by decide +kernel

end RosserMediumSqrtCertificates

-- Source: Solutions/RosserMediumSqrtCertificates/C04.lean
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RosserMediumSqrtCertificates

def groups04 : List RosserMediumSqrtChain.Group := [
⟨8393141, 9441717, 649622041016209911, 644860479445105130, [
⟨8393141, 8439921, 649622041016209911, 649397239685832308⟩,
⟨8439921, 8486896, 649397239685832308, 649171546592986032⟩,
⟨8486896, 8534067, 649171546592986032, 648944199553394650⟩,
⟨8534067, 8581435, 648944199553394650, 648716294397739179⟩,
⟨8581435, 8629000, 648716294397739179, 648491382694677639⟩,
⟨8629000, 8655285, 648491382694677639, 648368258820245985⟩,
⟨8655285, 8703156, 648368258820245985, 648144187113516358⟩,
⟨8703156, 8751226, 648144187113516358, 647919935666716139⟩,
⟨8751226, 8799495, 647919935666716139, 647696104767043536⟩,
⟨8799495, 8847963, 647696104767043536, 647474535905142950⟩,
⟨8847963, 8896632, 647474535905142950, 647254184951087660⟩,
⟨8896632, 8917429, 647254184951087660, 647159579684188413⟩,
⟨8917429, 8966384, 647159579684188413, 646938076091625024⟩,
⟨8966384, 9015540, 646938076091625024, 646719152212187950⟩,
⟨9015540, 9064898, 646719152212187950, 646500711521032371⟩,
⟨9064898, 9114459, 646500711521032371, 646280471529965239⟩,
⟨9114459, 9164223, 646280471529965239, 646062140624569707⟩,
⟨9164223, 9179573, 646062140624569707, 645992761887155695⟩,
⟨9179573, 9229603, 645992761887155695, 645772151467604372⟩,
⟨9229603, 9279838, 645772151467604372, 645553294544048459⟩,
⟨9279838, 9330277, 645553294544048459, 645336179793622775⟩,
⟨9330277, 9380922, 645336179793622775, 645118032042648278⟩,
⟨9380922, 9431773, 645118032042648278, 644902506676211138⟩,
⟨9431773, 9441717, 644902506676211138, 644860479445105130⟩
]⟩,
⟨9441717, 10490293, 644860479445105130, 640661832631617762, [
⟨9441717, 9492815, 644860479445105130, 644644727595490744⟩,
⟨9492815, 9544120, 644644727595490744, 644428580877861743⟩,
⟨9544120, 9595633, 644428580877861743, 644209633228891664⟩,
⟨9595633, 9647355, 644209633228891664, 643994878968604498⟩,
⟨9647355, 9699285, 643994878968604498, 643780872146745819⟩,
⟨9699285, 9703861, 643780872146745819, 643762159280367300⟩,
⟨9703861, 9756019, 643762159280367300, 643547096491071074⟩,
⟨9756019, 9808387, 643547096491071074, 643332471541607658⟩,
⟨9808387, 9860966, 643332471541607658, 643120758930702944⟩,
⟨9860966, 9913757, 643120758930702944, 642909786977573398⟩,
⟨9913757, 9966005, 642909786977573398, 642701032205415221⟩,
⟨9966005, 10019217, 642701032205415221, 642491327571583074⟩,
⟨10019217, 10072642, 642491327571583074, 642277428399325087⟩,
⟨10072642, 10126280, 642277428399325087, 642064865584659636⟩,
⟨10126280, 10180132, 642064865584659636, 641854950242430838⟩,
⟨10180132, 10228149, 641854950242430838, 641670049907859616⟩,
⟨10228149, 10282407, 641670049907859616, 641458410907053462⟩,
⟨10282407, 10336881, 641458410907053462, 641249390816978557⟩,
⟨10336881, 10391571, 641249390816978557, 641040484398700588⟩,
⟨10391571, 10446478, 641040484398700588, 640829234889640952⟩,
⟨10446478, 10490293, 640829234889640952, 640661832631617762⟩
]⟩,
⟨10490293, 11538869, 640661832631617762, 636907504235119639, [
⟨10490293, 10545591, 640661832631617762, 640454460604996027⟩,
⟨10545591, 10601107, 640454460604996027, 640245817972466640⟩,
⟨10601107, 10656842, 640245817972466640, 640038099214273931⟩,
⟨10656842, 10712797, 640038099214273931, 639827699148981069⟩,
⟨10712797, 10752437, 639827699148981069, 639681955843371029⟩,
⟨10752437, 10808768, 639681955843371029, 639478171258790702⟩,
⟨10808768, 10865320, 639478171258790702, 639270968611949814⟩,
⟨10865320, 10922094, 639270968611949814, 639066259444248945⟩,
⟨10922094, 10979090, 639066259444248945, 638860164555179482⟩,
⟨10979090, 11014581, 638860164555179482, 638733935404780014⟩,
⟨11014581, 11071939, 638733935404780014, 638529160308601927⟩,
⟨11071939, 11129521, 638529160308601927, 638325155660143965⟩,
⟨11129521, 11187327, 638325155660143965, 638118335902523394⟩,
⟨11187327, 11245358, 638118335902523394, 637916801520202981⟩,
⟨11245358, 11276725, 637916801520202981, 637808440933257377⟩,
⟨11276725, 11335104, 637808440933257377, 637605552576692797⟩,
⟨11335104, 11393709, 637605552576692797, 637405006431489802⟩,
⟨11393709, 11452541, 637405006431489802, 637203766851597542⟩,
⟨11452541, 11511601, 637203766851597542, 637001234079227929⟩,
⟨11511601, 11538869, 637001234079227929, 636907504235119639⟩
]⟩,
⟨11538869, 12587445, 636907504235119639, 633517020609019644, [
⟨11538869, 11598263, 636907504235119639, 636705866260048279⟩,
⟨11598263, 11657886, 636705866260048279, 636502750482485638⟩,
⟨11657886, 11717739, 636502750482485638, 636303518788898127⟩,
⟨11717739, 11777822, 636303518788898127, 636105686319222377⟩,
⟨11777822, 11801013, 636105686319222377, 636026753153968043⟩,
⟨11801013, 11861416, 636026753153968043, 635828468908672047⟩,
⟨11861416, 11922050, 635828468908672047, 635629168855583516⟩,
⟨11922050, 11982917, 635629168855583516, 635429399822568710⟩,
⟨11982917, 12044017, 635429399822568710, 635232084519042943⟩,
⟨12044017, 12063157, 635232084519042943, 635168900207864318⟩,
⟨12063157, 12124563, 635168900207864318, 634972875645692354⟩,
⟨12124563, 12186204, 634972875645692354, 634775810296019985⟩,
⟨12186204, 12248079, 634775810296019985, 634578971331334080⟩,
⟨12248079, 12310190, 634578971331334080, 634380916831731130⟩,
⟨12310190, 12325301, 634380916831731130, 634331991925705877⟩,
⟨12325301, 12387705, 634331991925705877, 634135820391383129⟩,
⟨12387705, 12450346, 634135820391383129, 633939362828035865⟩,
⟨12450346, 12513225, 633939362828035865, 633746439438122903⟩,
⟨12513225, 12576342, 633746439438122903, 633551562691442614⟩,
⟨12576342, 12587445, 633551562691442614, 633517020609019644⟩
]⟩,
⟨12587445, 13636021, 633517020609019644, 630435602642834042, [
⟨12587445, 12650842, 633517020609019644, 633321358097019528⟩,
⟨12650842, 12714478, 633321358097019528, 633127039794922460⟩,
⟨12714478, 12778354, 633127039794922460, 632930620363638054⟩,
⟨12778354, 12842471, 632930620363638054, 632737368034064502⟩,
⟨12842471, 12849589, 632737368034064502, 632715302033720212⟩,
⟨12849589, 12913974, 632715302033720212, 632524115218743995⟩,
⟨12913974, 12978601, 632524115218743995, 632333305750574609⟩,
⟨12978601, 13043470, 632333305750574609, 632141169412936996⟩,
⟨13043470, 13108582, 632141169412936996, 631951353929892932⟩,
⟨13108582, 13111733, 631951353929892932, 631942002609679466⟩,
⟨13111733, 13177100, 631942002609679466, 631750975239921009⟩,
⟨13177100, 13242712, 631750975239921009, 631559131631102955⟩,
⟨13242712, 13308569, 631559131631102955, 631368252009791574⟩,
⟨13308569, 13373877, 631368252009791574, 631179643778610687⟩,
⟨13373877, 13440222, 631179643778610687, 630989428918850693⟩,
⟨13440222, 13506814, 630989428918850693, 630801523118290909⟩,
⟨13506814, 13573653, 630801523118290909, 630613060458901781⟩,
⟨13573653, 13636021, 630613060458901781, 630435602642834042⟩
]⟩,
⟨13636021, 14684597, 630435602642834042, 627603372870760558, [
⟨13636021, 13703339, 630435602642834042, 630246217071191844⟩,
⟨13703339, 13770906, 630246217071191844, 630057496624310729⟩,
⟨13770906, 13838723, 630057496624310729, 629869345931709014⟩,
⟨13838723, 13898165, 629869345931709014, 629702684235769991⟩,
⟨13898165, 13966452, 629702684235769991, 629515771940745280⟩,
⟨13966452, 14034990, 629515771940745280, 629329746098432336⟩,
⟨14034990, 14103780, 629329746098432336, 629143607791633904⟩,
⟨14103780, 14160309, 629143607791633904, 628989989724386076⟩,
⟨14160309, 14229559, 628989989724386076, 628806170509011793⟩,
⟨14229559, 14299063, 628806170509011793, 628618140954451303⟩,
⟨14299063, 14368822, 628618140954451303, 628430996380920966⟩,
⟨14368822, 14422453, 628430996380920966, 628287999515275726⟩,
⟨14422453, 14492663, 628287999515275726, 628103636994621374⟩,
⟨14492663, 14563129, 628103636994621374, 627919271890582438⟩,
⟨14563129, 14633852, 627919271890582438, 627735632519739805⟩,
⟨14633852, 14684597, 627735632519739805, 627603372870760558⟩
]⟩,
⟨14684597, 15733173, 627603372870760558, 624993475343832095, [
⟨14684597, 14755762, 627603372870760558, 627419600674982649⟩,
⟨14755762, 14827185, 627419600674982649, 627235914500896877⟩,
⟨14827185, 14898867, 627235914500896877, 627053165146187059⟩,
⟨14898867, 14946741, 627053165146187059, 626931951169082587⟩,
⟨14946741, 15018856, 626931951169082587, 626750920682728669⟩,
⟨15018856, 15091232, 626750920682728669, 626568270313789577⟩,
⟨15091232, 15163870, 626568270313789577, 626386468475964681⟩,
⟨15163870, 15208885, 626386468475964681, 626275194538062638⟩,
⟨15208885, 15281947, 626275194538062638, 626092213616162860⟩,
⟨15281947, 15355272, 626092213616162860, 625911098965898968⟩,
⟨15355272, 15428861, 625911098965898968, 625733299147169298⟩,
⟨15428861, 15471029, 625733299147169298, 625631043489978894⟩,
⟨15471029, 15545033, 625631043489978894, 625448922298720717⟩,
⟨15545033, 15619303, 625448922298720717, 625267277923129644⟩,
⟨15619303, 15693839, 625267277923129644, 625087389973063447⟩,
⟨15693839, 15733173, 625087389973063447, 624993475343832095⟩
]⟩,
⟨15733173, 16781749, 624993475343832095, 622569849451073503, [
⟨15733173, 15808116, 624993475343832095, 624815242597763366⟩,
⟨15808116, 15883326, 624815242597763366, 624633847720512589⟩,
⟨15883326, 15958805, 624633847720512589, 624456147128403550⟩,
⟨15958805, 15995317, 624456147128403550, 624370010552637581⟩,
⟨15995317, 16071194, 624370010552637581, 624193004543224124⟩,
⟨16071194, 16147341, 624193004543224124, 624014637817405259⟩,
⟨16147341, 16223759, 624014637817405259, 623837744069048745⟩,
⟨16223759, 16257461, 623837744069048745, 623759887648544442⟩,
⟨16257461, 16334269, 623759887648544442, 623583948254701569⟩,
⟨16334269, 16411349, 623583948254701569, 623408051689647754⟩,
⟨16411349, 16488702, 623408051689647754, 623230981846801491⟩,
⟨16488702, 16519605, 623230981846801491, 623160482904795884⟩,
⟨16519605, 16597340, 623160482904795884, 622985060924413686⟩,
⟨16597340, 16675349, 622985060924413686, 622809082160664985⟩,
⟨16675349, 16753633, 622809082160664985, 622633194916831325⟩,
⟨16753633, 16781749, 622633194916831325, 622569849451073503⟩
]⟩
]

theorem c04 : RosserMediumSqrtChain.allGroups groups04 = true :=
  by decide +kernel

end RosserMediumSqrtCertificates

-- Source: Solutions/RosserMediumSqrtCertificates/C05.lean
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RosserMediumSqrtCertificates

def groups05 : List RosserMediumSqrtChain.Group := [
⟨16781749, 17830325, 622569849451073503, 620307140828442929, [
⟨16781749, 16860408, 622569849451073503, 622394919279883262⟩,
⟨16860408, 16939343, 622394919279883262, 622220524512753669⟩,
⟨16939343, 17018555, 622220524512753669, 622043214566083701⟩,
⟨17018555, 17043893, 622043214566083701, 621987810219183115⟩,
⟨17043893, 17123471, 621987810219183115, 621813547858983699⟩,
⟨17123471, 17203328, 621813547858983699, 621643040507903565⟩,
⟨17203328, 17283464, 621643040507903565, 621469658891764737⟩,
⟨17283464, 17306037, 621469658891764737, 621419748825212984⟩,
⟨17306037, 17386532, 621419748825212984, 621245843829648037⟩,
⟨17386532, 17467307, 621245843829648037, 621072684421409536⟩,
⟨17467307, 17548364, 621072684421409536, 620897855144790188⟩,
⟨17548364, 17568181, 620897855144790188, 620856023142829124⟩,
⟨17568181, 17649588, 620856023142829124, 620683845091702477⟩,
⟨17649588, 17731278, 620683845091702477, 620513212858078882⟩,
⟨17731278, 17813251, 620513212858078882, 620342017509970183⟩,
⟨17813251, 17830325, 620342017509970183, 620307140828442929⟩
]⟩,
⟨17830325, 18878901, 620307140828442929, 618191470313071706, [
⟨17830325, 17912642, 620307140828442929, 620136740802339917⟩,
⟨17912642, 17995244, 620136740802339917, 619963164245914779⟩,
⟨17995244, 18078131, 619963164245914779, 619794350218188225⟩,
⟨18078131, 18092469, 619794350218188225, 619766180668691176⟩,
⟨18092469, 18175692, 619766180668691176, 619595899138686736⟩,
⟨18175692, 18259202, 619595899138686736, 619425700270022455⟩,
⟨18259202, 18342999, 619425700270022455, 619254594311190927⟩,
⟨18342999, 18354613, 619254594311190927, 619231375356325241⟩,
⟨18354613, 18438738, 619231375356325241, 619063201218725604⟩,
⟨18438738, 18523152, 619063201218725604, 618896170976693748⟩,
⟨18523152, 18607856, 618896170976693748, 618726215756118631⟩,
⟨18607856, 18616757, 618726215756118631, 618708364669173387⟩,
⟨18616757, 18701782, 618708364669173387, 618540471139079078⟩,
⟨18701782, 18787098, 618540471139079078, 618371375367470856⟩,
⟨18787098, 18872706, 618371375367470856, 618203162316154395⟩,
⟨18872706, 18878901, 618203162316154395, 618191470313071706⟩
]⟩,
⟨18878901, 19927477, 618191470313071706, 616204378430454259, [
⟨18878901, 18964822, 618191470313071706, 618024156182348872⟩,
⟨18964822, 19051036, 618024156182348872, 617857187971988967⟩,
⟨19051036, 19137544, 617857187971988967, 617690600119090442⟩,
⟨19137544, 19141045, 617690600119090442, 617684371399455969⟩,
⟨19141045, 19227859, 617684371399455969, 617518673409142357⟩,
⟨19227859, 19314969, 617518673409142357, 617351910648511607⟩,
⟨19314969, 19402374, 617351910648511607, 617185178135323119⟩,
⟨19402374, 19403189, 617185178135323119, 617183524065743666⟩,
⟨19403189, 19490894, 617183524065743666, 617017464429382905⟩,
⟨19490894, 19578896, 617017464429382905, 616854313171792512⟩,
⟨19578896, 19665333, 616854313171792512, 616692684971178472⟩,
⟨19665333, 19753925, 616692684971178472, 616526500471649066⟩,
⟨19753925, 19842816, 616526500471649066, 616361384365863524⟩,
⟨19842816, 19927477, 616361384365863524, 616204378430454259⟩
]⟩,
⟨19927477, 20976053, 616204378430454259, 614331988623225986, [
⟨19927477, 20016953, 616204378430454259, 616039891757302926⟩,
⟨20016953, 20106730, 616039891757302926, 615874740484852566⟩,
⟨20106730, 20189621, 615874740484852566, 615724431913202793⟩,
⟨20189621, 20279978, 615724431913202793, 615562755032320453⟩,
⟨20279978, 20370639, 615562755032320453, 615399387409021764⟩,
⟨20370639, 20451765, 615399387409021764, 615255979604990809⟩,
⟨20451765, 20543001, 615255979604990809, 615093041984630101⟩,
⟨20543001, 20634542, 615093041984630101, 614930184055904142⟩,
⟨20634542, 20713909, 614930184055904142, 614788295332917118⟩,
⟨20713909, 20806021, 614788295332917118, 614627156152495531⟩,
⟨20806021, 20898440, 614627156152495531, 614465771603876582⟩,
⟨20898440, 20976053, 614465771603876582, 614331988623225986⟩
]⟩,
⟨20976053, 22024629, 614331988623225986, 612556538589334388, [
⟨20976053, 21069038, 614331988623225986, 614169122164566071⟩,
⟨21069038, 21162332, 614169122164566071, 614010158277521247⟩,
⟨21162332, 21238197, 614010158277521247, 613880621878578303⟩,
⟨21238197, 21332052, 613880621878578303, 613718902422634622⟩,
⟨21332052, 21426218, 613718902422634622, 613559572527603479⟩,
⟨21426218, 21500341, 613559572527603479, 613431917630059447⟩,
⟨21500341, 21595063, 613431917630059447, 613273570670979836⟩,
⟨21595063, 21690098, 613273570670979836, 613114000375123280⟩,
⟨21690098, 21762485, 613114000375123280, 612992891324085978⟩,
⟨21762485, 21858072, 612992891324085978, 612833186191084074⟩,
⟨21858072, 21953974, 612833186191084074, 612672601074355959⟩,
⟨21953974, 22024629, 612672601074355959, 612556538589334388⟩
]⟩,
⟨22024629, 23073205, 612556538589334388, 610878040780065502, [
⟨22024629, 22121079, 612556538589334388, 612399703351957739⟩,
⟨22121079, 22217845, 612399703351957739, 612243233297993770⟩,
⟨22217845, 22286773, 612243233297993770, 612131895226787658⟩,
⟨22286773, 22384082, 612131895226787658, 611974465001061928⟩,
⟨22384082, 22481710, 611974465001061928, 611818170390797042⟩,
⟨22481710, 22548917, 611818170390797042, 611709649900541449⟩,
⟨22548917, 22647083, 611709649900541449, 611552476799946604⟩,
⟨22647083, 22745570, 611552476799946604, 611394518792659031⟩,
⟨22745570, 22811061, 611394518792659031, 611291860114809714⟩,
⟨22811061, 22910082, 611291860114809714, 611134836375958342⟩,
⟨22910082, 23009425, 611134836375958342, 610978159575527744⟩,
⟨23009425, 23073205, 610978159575527744, 610878040780065502⟩
]⟩,
⟨23073205, 24121781, 610878040780065502, 609283191128933240, [
⟨23073205, 23173078, 610878040780065502, 610722168818570651⟩,
⟨23173078, 23273275, 610722168818570651, 610567875875435125⟩,
⟨23273275, 23335349, 610567875875435125, 610471546618668817⟩,
⟨23335349, 23436072, 610471546618668817, 610317782806658740⟩,
⟨23436072, 23537121, 610317782806658740, 610162561464626243⟩,
⟨23537121, 23597493, 610162561464626243, 610070812761947443⟩,
⟨23597493, 23699064, 610070812761947443, 609915865051320085⟩,
⟨23699064, 23800962, 609915865051320085, 609762803173569881⟩,
⟨23800962, 23859637, 609762803173569881, 609675657050857751⟩,
⟨23859637, 23962053, 609675657050857751, 609521538931166746⟩,
⟨23962053, 24064798, 609521538931166746, 609367003526918806⟩,
⟨24064798, 24121781, 609367003526918806, 609283191128933240⟩
]⟩,
⟨24121781, 25170357, 609283191128933240, 607760702849490008, [
⟨24121781, 24225039, 609283191128933240, 609129385505088826⟩,
⟨24225039, 24328629, 609129385505088826, 608975244416130523⟩,
⟨24328629, 24383925, 608975244416130523, 608893765790229847⟩,
⟨24383925, 24488024, 608893765790229847, 608741361628001227⟩,
⟨24488024, 24592456, 608741361628001227, 608589395134138437⟩,
⟨24592456, 24646069, 608589395134138437, 608511902986324405⟩,
⟨24646069, 24751006, 608511902986324405, 608358749259525301⟩,
⟨24751006, 24856278, 608358749259525301, 608207999295615842⟩,
⟨24856278, 24908213, 608207999295615842, 608133206545906652⟩,
⟨24908213, 25013986, 608133206545906652, 607981907681425540⟩,
⟨25013986, 25120096, 607981907681425540, 607830195456767074⟩,
⟨25120096, 25170357, 607830195456767074, 607760702849490008⟩
]⟩
]

theorem c05 : RosserMediumSqrtChain.allGroups groups05 = true :=
  by decide +kernel

end RosserMediumSqrtCertificates

-- Source: Solutions/RosserMediumSqrtCertificates/C06.lean
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RosserMediumSqrtCertificates

def groups06 : List RosserMediumSqrtChain.Group := [
⟨25170357, 26218933, 607760702849490008, 606309483343949246, [
⟨25170357, 25276964, 607760702849490008, 607611213774465364⟩,
⟨25276964, 25383909, 607611213774465364, 607461599167872976⟩,
⟨25383909, 25432501, 607461599167872976, 607393751420347719⟩,
⟨25432501, 25539940, 607393751420347719, 607243173659673616⟩,
⟨25539940, 25647719, 607243173659673616, 607092816280479335⟩,
⟨25647719, 25694645, 607092816280479335, 607028802667358845⟩,
⟨25694645, 25802913, 607028802667358845, 606878223387078787⟩,
⟨25802913, 25911523, 606878223387078787, 606728733511632030⟩,
⟨25911523, 25956789, 606728733511632030, 606666482077787790⟩,
⟨25956789, 26065884, 606666482077787790, 606516952462972444⟩,
⟨26065884, 26175323, 606516952462972444, 606368711650876024⟩,
⟨26175323, 26218933, 606368711650876024, 606309483343949246⟩
]⟩,
⟨26218933, 27267509, 606309483343949246, 604920034816125610, [
⟨26218933, 26328854, 606309483343949246, 606161652141870061⟩,
⟨26328854, 26439120, 606161652141870061, 606012726406597736⟩,
⟨26439120, 26481077, 606012726406597736, 605956914843869285⟩,
⟨26481077, 26591821, 605956914843869285, 605807340820068404⟩,
⟨26591821, 26702912, 605807340820068404, 605660109352715686⟩,
⟨26702912, 26743221, 605660109352715686, 605607189992970198⟩,
⟨26743221, 26854786, 605607189992970198, 605460388315177940⟩,
⟨26854786, 26966700, 605460388315177940, 605312004194807010⟩,
⟨26966700, 27005365, 605312004194807010, 605261358345020708⟩,
⟨27005365, 27117750, 605261358345020708, 605114162813939870⟩,
⟨27117750, 27230485, 605114162813939870, 604967588531708185⟩,
⟨27230485, 27267509, 604967588531708185, 604920034816125610⟩
]⟩,
⟨27267509, 28316085, 604920034816125610, 603588448689875228, [
⟨27267509, 27380711, 604920034816125610, 604774756246602313⟩,
⟨27380711, 27494265, 604774756246602313, 604628435660439713⟩,
⟨27494265, 27529653, 604628435660439713, 604582747510770760⟩,
⟨27529653, 27643670, 604582747510770760, 604435513494796458⟩,
⟨27643670, 27758041, 604435513494796458, 604290407006011126⟩,
⟨27758041, 27791797, 604290407006011126, 604247765145199255⟩,
⟨27791797, 27906627, 604247765145199255, 604102717254474603⟩,
⟨27906627, 28021813, 604102717254474603, 603957002629313861⟩,
⟨28021813, 28053941, 603957002629313861, 603916786816370693⟩,
⟨28053941, 28169583, 603916786816370693, 603772289862169901⟩,
⟨28169583, 28285582, 603772289862169901, 603627266203948141⟩,
⟨28285582, 28316085, 603627266203948141, 603588448689875228⟩
]⟩,
⟨28316085, 29364661, 603588448689875228, 602313348381215659, [
⟨28316085, 28432536, 603588448689875228, 603445281918614625⟩,
⟨28432536, 28549346, 603445281918614625, 603300658915157255⟩,
⟨28549346, 28578229, 603300658915157255, 603265134087882538⟩,
⟨28578229, 28695488, 603265134087882538, 603121100867508975⟩,
⟨28695488, 28813107, 603121100867508975, 602978696889480105⟩,
⟨28813107, 28840373, 602978696889480105, 602945606683940937⟩,
⟨28840373, 28958438, 602945606683940937, 602801831146231068⟩,
⟨28958438, 29076865, 602801831146231068, 602659589699080937⟩,
⟨29076865, 29102517, 602659589699080937, 602628431598422896⟩,
⟨29102517, 29221386, 602628431598422896, 602486294287371468⟩,
⟨29221386, 29340618, 602486294287371468, 602342979869556189⟩,
⟨29340618, 29364661, 602342979869556189, 602313348381215659⟩
]⟩,
⟨29364661, 30413237, 602313348381215659, 601083779853159640, [
⟨29364661, 29484332, 602313348381215659, 602172676007635816⟩,
⟨29484332, 29604368, 602172676007635816, 602030283375822569⟩,
⟨29604368, 29626805, 602030283375822569, 602003491526872211⟩,
⟨29626805, 29747276, 602003491526872211, 601860830399608509⟩,
⟨29747276, 29868114, 601860830399608509, 601719409321847657⟩,
⟨29868114, 29888949, 601719409321847657, 601694558604578763⟩,
⟨29888949, 30010219, 601694558604578763, 601551895334675139⟩,
⟨30010219, 30131857, 601551895334675139, 601409700809998987⟩,
⟨30131857, 30151093, 601409700809998987, 601387114562814881⟩,
⟨30151093, 30273160, 601387114562814881, 601246279850927162⟩,
⟨30273160, 30395597, 601246279850927162, 601104617427745469⟩,
⟨30395597, 30413237, 601104617427745469, 601083779853159640⟩
]⟩,
⟨30413237, 31461813, 601083779853159640, 599906131666743575, [
⟨30413237, 30536099, 601083779853159640, 600944685286222242⟩,
⟨30536099, 30659333, 600944685286222242, 600802547531186782⟩,
⟨30659333, 30675381, 600802547531186782, 600783955989797885⟩,
⟨30675381, 30799036, 600783955989797885, 600644571767407364⟩,
⟨30799036, 30861050, 600644571767407364, 600573933112645747⟩,
⟨30861050, 30937525, 600573933112645747, 600487563429489501⟩,
⟨30937525, 31061972, 600487563429489501, 600349737026864460⟩,
⟨31061972, 31186794, 600349737026864460, 600211240112559976⟩,
⟨31186794, 31199669, 600211240112559976, 600196847461917740⟩,
⟨31199669, 31324906, 600196847461917740, 600057039247429328⟩,
⟨31324906, 31450519, 600057039247429328, 599918241960560601⟩,
⟨31450519, 31461813, 599918241960560601, 599906131666743575⟩
]⟩,
⟨31461813, 32510389, 599906131666743575, 598768695229305611, [
⟨31461813, 31587838, 599906131666743575, 599767461828645112⟩,
⟨31587838, 31714242, 599767461828645112, 599628787463196645⟩,
⟨31714242, 31723957, 599628787463196645, 599618654831552476⟩,
⟨31723957, 31850769, 599618654831552476, 599479798535520837⟩,
⟨31850769, 31977961, 599479798535520837, 599340869130536720⟩,
⟨31977961, 31986101, 599340869130536720, 599332586166860025⟩,
⟨31986101, 32113698, 599332586166860025, 599193868774982043⟩,
⟨32113698, 32241676, 599193868774982043, 599056979943806240⟩,
⟨32241676, 32248245, 599056979943806240, 599049790164999676⟩,
⟨32248245, 32376625, 599049790164999676, 598911818047388302⟩,
⟨32376625, 32505388, 598911818047388302, 598773889450767428⟩,
⟨32505388, 32510389, 598773889450767428, 598768695229305611⟩
]⟩,
⟨32510389, 33558965, 598768695229305611, 597670862804663679, [
⟨32510389, 32639551, 598768695229305611, 598630869925297165⟩,
⟨32639551, 32769098, 598630869925297165, 598494225340352470⟩,
⟨32769098, 32772533, 598494225340352470, 598490810156146043⟩,
⟨32772533, 32902476, 598490810156146043, 598354077664011590⟩,
⟨32902476, 33032805, 598354077664011590, 598216917110555752⟩,
⟨33032805, 33034677, 598216917110555752, 598215341609719701⟩,
⟨33034677, 33165399, 598215341609719701, 598078925539015120⟩,
⟨33165399, 33296508, 598078925539015120, 597942393144133355⟩,
⟨33296508, 33296821, 597942393144133355, 597942177647812939⟩,
⟨33296821, 33428320, 597942177647812939, 597804995652354055⟩,
⟨33428320, 33558965, 597804995652354055, 597670862804663679⟩
]⟩
]

theorem c06 : RosserMediumSqrtChain.allGroups groups06 = true :=
  by decide +kernel

end RosserMediumSqrtCertificates

-- Source: Solutions/RosserMediumSqrtCertificates/C07.lean
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RosserMediumSqrtCertificates

def groups07 : List RosserMediumSqrtChain.Group := [
⟨33558965, 34607541, 597670862804663679, 596614786391817358, [
⟨33558965, 33691239, 597670862804663679, 597535596427424837⟩,
⟨33691239, 33821109, 597535596427424837, 597402124948861925⟩,
⟨33821109, 33954158, 597402124948861925, 597267788349277677⟩,
⟨33954158, 34083253, 597267788349277677, 597138107839156659⟩,
⟨34083253, 34217074, 597138107839156659, 597004234607196344⟩,
⟨34217074, 34345397, 597004234607196344, 596876700935597128⟩,
⟨34345397, 34479989, 596876700935597128, 596742469377314880⟩,
⟨34479989, 34607541, 596742469377314880, 596614786391817358⟩
]⟩,
⟨34607541, 35656117, 596614786391817358, 595592058120009829, [
⟨34607541, 34742903, 596614786391817358, 596482403265045460⟩,
⟨34742903, 34869685, 596482403265045460, 596356973363273162⟩,
⟨34869685, 35005816, 596356973363273162, 596223011626427597⟩,
⟨35005816, 35131829, 596223011626427597, 596100545433315194⟩,
⟨35131829, 35268726, 596100545433315194, 595966489681945326⟩,
⟨35268726, 35393973, 595966489681945326, 595844851439797432⟩,
⟨35393973, 35531636, 595844851439797432, 595711945430556679⟩,
⟨35531636, 35656117, 595711945430556679, 595592058120009829⟩
]⟩,
⟨35656117, 36704693, 595592058120009829, 594601445636621603, [
⟨35656117, 35794544, 595592058120009829, 595458919035048144⟩,
⟨35794544, 35918261, 595458919035048144, 595341935650429705⟩,
⟨35918261, 36057450, 595341935650429705, 595209292753088377⟩,
⟨36057450, 36180405, 595209292753088377, 595092894706209749⟩,
⟨36180405, 36320355, 595092894706209749, 594960644646817864⟩,
⟨36320355, 36442549, 594960644646817864, 594845722467713824⟩,
⟨36442549, 36583259, 594845722467713824, 594713825293901391⟩,
⟨36583259, 36704693, 594713825293901391, 594601445636621603⟩
]⟩,
⟨36704693, 37753269, 594601445636621603, 593640971507169334, [
⟨36704693, 36846162, 594601445636621603, 594470333399087826⟩,
⟨36846162, 36966837, 594470333399087826, 594359959562117027⟩,
⟨36966837, 37109063, 594359959562117027, 594227535880067901⟩,
⟨37109063, 37228981, 594227535880067901, 594117345241622802⟩,
⟨37228981, 37371963, 594117345241622802, 593987373059335802⟩,
⟨37371963, 37491125, 593987373059335802, 593878778186439014⟩,
⟨37491125, 37634861, 593878778186439014, 593748262705867127⟩,
⟨37634861, 37753269, 593748262705867127, 593640971507169334⟩
]⟩,
⟨37753269, 38801845, 593640971507169334, 592708975279759594, [
⟨37753269, 37897758, 593640971507169334, 593512058150274214⟩,
⟨37897758, 38015413, 593512058150274214, 593406739510561502⟩,
⟨38015413, 38160654, 593406739510561502, 593276537139323094⟩,
⟨38160654, 38277557, 593276537139323094, 593171626039007911⟩,
⟨38277557, 38423549, 593171626039007911, 593042118017453600⟩,
⟨38423549, 38539701, 593042118017453600, 592939627549178033⟩,
⟨38539701, 38686442, 592939627549178033, 592811389205544890⟩,
⟨38686442, 38801845, 592811389205544890, 592708975279759594⟩
]⟩,
⟨38801845, 39850421, 592708975279759594, 591803503897076155, [
⟨38801845, 38949334, 592708975279759594, 592579472516239419⟩,
⟨38949334, 39063989, 592579472516239419, 592480643796558594⟩,
⟨39063989, 39212225, 592480643796558594, 592352421164266208⟩,
⟨39212225, 39326133, 592352421164266208, 592252450430274875⟩,
⟨39326133, 39475114, 592252450430274875, 592124590489569557⟩,
⟨39475114, 39588277, 592124590489569557, 592027237711659078⟩,
⟨39588277, 39738002, 592027237711659078, 591899002214431335⟩,
⟨39738002, 39850421, 591899002214431335, 591803503897076155⟩
]⟩,
⟨39850421, 40898997, 591803503897076155, 590926831851563951, [
⟨39850421, 40000889, 591803503897076155, 591677006369207561⟩,
⟨40000889, 40112565, 591677006369207561, 591582849507372676⟩,
⟨40112565, 40263775, 591582849507372676, 591456340807164923⟩,
⟨40263775, 40374709, 591456340807164923, 591361803527954193⟩,
⟨40374709, 40526659, 591361803527954193, 591235243393024319⟩,
⟨40526659, 40636853, 591235243393024319, 591144922440212944⟩,
⟨40636853, 40789543, 591144922440212944, 591016814793111991⟩,
⟨40789543, 40898997, 591016814793111991, 590926831851563951⟩
]⟩,
⟨40898997, 41947573, 590926831851563951, 590076637264097077, [
⟨40898997, 41052425, 590926831851563951, 590801278489602386⟩,
⟨41052425, 41161141, 590801278489602386, 590711659153056811⟩,
⟨41161141, 41315306, 590711659153056811, 590586190573977001⟩,
⟨41315306, 41423285, 590586190573977001, 590498927392228631⟩,
⟨41423285, 41578186, 590498927392228631, 590373243524740526⟩,
⟨41578186, 41685429, 590373243524740526, 590287484738209017⟩,
⟨41685429, 41841064, 590287484738209017, 590161082847144605⟩,
⟨41841064, 41947573, 590161082847144605, 590076637264097077⟩
]⟩
]

theorem c07 : RosserMediumSqrtChain.allGroups groups07 = true :=
  by decide +kernel

end RosserMediumSqrtCertificates

-- Source: Solutions/RosserMediumSqrtCertificates/C08.lean
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RosserMediumSqrtCertificates

def groups08 : List RosserMediumSqrtChain.Group := [
⟨41947573, 42996149, 590076637264097077, 589248435453087914, [
⟨41947573, 42103942, 590076637264097077, 589951968496210917⟩,
⟨42103942, 42209717, 589951968496210917, 589867128141558409⟩,
⟨42209717, 42366818, 589867128141558409, 589741644613150673⟩,
⟨42366818, 42471861, 589741644613150673, 589658596224729696⟩,
⟨42471861, 42629693, 589658596224729696, 589534484502415710⟩,
⟨42629693, 42734005, 589534484502415710, 589452527498736555⟩,
⟨42734005, 42892567, 589452527498736555, 589328723610337644⟩,
⟨42892567, 42996149, 589328723610337644, 589248435453087914⟩
]⟩,
⟨42996149, 44044725, 589248435453087914, 588441800496394462, [
⟨42996149, 43155440, 589248435453087914, 589124814482914351⟩,
⟨43155440, 43258293, 589124814482914351, 589044808963332386⟩,
⟨43258293, 43418312, 589044808963332386, 588921014798461629⟩,
⟨43418312, 43520437, 588921014798461629, 588842035444079256⟩,
⟨43520437, 43681183, 588842035444079256, 588719229305786526⟩,
⟨43681183, 43782581, 588719229305786526, 588641868336890346⟩,
⟨43782581, 43944053, 588641868336890346, 588519075740254460⟩,
⟨43944053, 44044725, 588519075740254460, 588441800496394462⟩
]⟩,
⟨44044725, 45093301, 588441800496394462, 587655667697371172, [
⟨44044725, 44206921, 588441800496394462, 588319393571503378⟩,
⟨44206921, 44306869, 588319393571503378, 588243467744363546⟩,
⟨44306869, 44469788, 588243467744363546, 588121335599715765⟩,
⟨44469788, 44569013, 588121335599715765, 588046952577067157⟩,
⟨44569013, 44732655, 588046952577067157, 587923879098299474⟩,
⟨44732655, 44831157, 587923879098299474, 587850428677899870⟩,
⟨44831157, 44995520, 587850428677899870, 587728417320114557⟩,
⟨44995520, 45093301, 587728417320114557, 587655667697371172⟩
]⟩,
⟨45093301, 46141877, 587655667697371172, 586888893523372925, [
⟨45093301, 45258385, 587655667697371172, 587533794512836763⟩,
⟨45258385, 45355445, 587533794512836763, 587461282970334866⟩,
⟨45355445, 45521248, 587461282970334866, 587339481022816820⟩,
⟨45521248, 45617589, 587339481022816820, 587268493491705556⟩,
⟨45617589, 45784110, 587268493491705556, 587147033101399268⟩,
⟨45784110, 45879733, 587147033101399268, 587078256268515662⟩,
⟨45879733, 46046971, 587078256268515662, 586956939380934026⟩,
⟨46046971, 46141877, 586956939380934026, 586888893523372925⟩
]⟩,
⟨46141877, 47190453, 586888893523372925, 586142591810862871, [
⟨46141877, 46309831, 586888893523372925, 586768533234317744⟩,
⟨46309831, 46404021, 586768533234317744, 586700881941318498⟩,
⟨46404021, 46572690, 586700881941318498, 586580407123378998⟩,
⟨46572690, 46666165, 586580407123378998, 586513221370113482⟩,
⟨46666165, 46835548, 586513221370113482, 586392897223504107⟩,
⟨46835548, 46928309, 586392897223504107, 586327246976358493⟩,
⟨46928309, 47098406, 586327246976358493, 586207992839994238⟩,
⟨47098406, 47190453, 586207992839994238, 586142591810862871⟩
]⟩,
⟨47190453, 48239029, 586142591810862871, 585416666329804210, [
⟨47190453, 47361262, 586142591810862871, 586023033573690985⟩,
⟨47361262, 47452597, 586023033573690985, 585959312720152645⟩,
⟨47452597, 47624117, 585959312720152645, 585839625830166052⟩,
⟨47624117, 47714741, 585839625830166052, 585777308380362147⟩,
⟨47714741, 47886971, 585777308380362147, 585657275733930546⟩,
⟨47886971, 47976885, 585657275733930546, 585595709849898007⟩,
⟨47976885, 48149824, 585595709849898007, 585477161642733097⟩,
⟨48149824, 48239029, 585477161642733097, 585416666329804210⟩
]⟩,
⟨48239029, 49287605, 585416666329804210, 584706092268928631, [
⟨48239029, 48412677, 585416666329804210, 585297307227824273⟩,
⟨48412677, 48501173, 585297307227824273, 585237050070218077⟩,
⟨48501173, 48675528, 585237050070218077, 585118589083477800⟩,
⟨48675528, 48763317, 585118589083477800, 585059887066091732⟩,
⟨48763317, 48938378, 585059887066091732, 584940912612012217⟩,
⟨48938378, 49025461, 584940912612012217, 584882542927586962⟩,
⟨49025461, 49201228, 584882542927586962, 584764074110329506⟩,
⟨49201228, 49287605, 584764074110329506, 584706092268928631⟩
]⟩,
⟨49287605, 50336181, 584706092268928631, 584010357270768802, [
⟨49287605, 49464076, 584706092268928631, 584587755557370490⟩,
⟨49464076, 49549749, 584587755557370490, 584530122149867470⟩,
⟨49549749, 49726923, 584530122149867470, 584412104100835738⟩,
⟨49726923, 49811893, 584412104100835738, 584355449798687873⟩,
⟨49811893, 49989770, 584355449798687873, 584237656135310177⟩,
⟨49989770, 50074037, 584237656135310177, 584182799001358821⟩,
⟨50074037, 50252615, 584182799001358821, 584065701621498150⟩,
⟨50252615, 50336181, 584065701621498150, 584010357270768802⟩
]⟩
]

theorem c08 : RosserMediumSqrtChain.allGroups groups08 = true :=
  by decide +kernel

end RosserMediumSqrtCertificates

-- Source: Solutions/RosserMediumSqrtCertificates/C09.lean
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RosserMediumSqrtCertificates

def groups09 : List RosserMediumSqrtChain.Group := [
⟨50336181, 51384757, 584010357270768802, 583332384589881076, [
⟨50336181, 50515460, 584010357270768802, 583893685340523931⟩,
⟨50515460, 50598325, 583893685340523931, 583839279300368957⟩,
⟨50598325, 50778304, 583839279300368957, 583722427606718359⟩,
⟨50778304, 50860469, 583722427606718359, 583668846951160981⟩,
⟨50860469, 51041147, 583668846951160981, 583553317743674846⟩,
⟨51041147, 51122613, 583553317743674846, 583500599282183512⟩,
⟨51122613, 51303989, 583500599282183512, 583384909418635775⟩,
⟨51303989, 51384757, 583384909418635775, 583332384589881076⟩
]⟩,
⟨51384757, 52433333, 583332384589881076, 582669715560012250, [
⟨51384757, 51566830, 583332384589881076, 583216241895921980⟩,
⟨51566830, 51646901, 583216241895921980, 583165343435212524⟩,
⟨51646901, 51829670, 583165343435212524, 583048573360230818⟩,
⟨51829670, 51909045, 583048573360230818, 582998846427132137⟩,
⟨51909045, 52092510, 582998846427132137, 582882719409108578⟩,
⟨52092510, 52171189, 582882719409108578, 582833782355626306⟩,
⟨52171189, 52355348, 582833782355626306, 582718438392290670⟩,
⟨52355348, 52433333, 582718438392290670, 582669715560012250⟩
]⟩,
⟨52433333, 53481909, 582669715560012250, 582021512945639338, [
⟨52433333, 52618186, 582669715560012250, 582554470217001476⟩,
⟨52618186, 52695477, 582554470217001476, 582506324664170113⟩,
⟨52695477, 52881022, 582506324664170113, 582390802009166406⟩,
⟨52881022, 52957621, 582390802009166406, 582343712322315258⟩,
⟨52957621, 53143858, 582343712322315258, 582228803791204373⟩,
⟨53143858, 53219765, 582228803791204373, 582181970235351816⟩,
⟨53219765, 53406693, 582181970235351816, 582066949014242896⟩,
⟨53406693, 53481909, 582066949014242896, 582021512945639338⟩
]⟩,
⟨53481909, 54530485, 582021512945639338, 581388538978784069, [
⟨53481909, 53669527, 582021512945639338, 581907218787142590⟩,
⟨53669527, 53744053, 581907218787142590, 581861844182935535⟩,
⟨53744053, 53932360, 581861844182935535, 581747781593374768⟩,
⟨53932360, 54006197, 581747781593374768, 581702801515975482⟩,
⟨54006197, 54195193, 581702801515975482, 581588978698118871⟩,
⟨54195193, 54268341, 581588978698118871, 581545311980567761⟩,
⟨54268341, 54458025, 581545311980567761, 581432186584213133⟩,
⟨54458025, 54530485, 581432186584213133, 581388538978784069⟩
]⟩,
⟨54530485, 55579061, 581388538978784069, 580767857237625032, [
⟨54530485, 54720855, 581388538978784069, 581274795248924858⟩,
⟨54720855, 54792629, 581274795248924858, 581232069029335971⟩,
⟨54792629, 54983685, 581232069029335971, 581118911948347912⟩,
⟨54983685, 55054773, 581118911948347912, 581076453909438699⟩,
⟨55054773, 55246515, 581076453909438699, 580962810935504541⟩,
⟨55246515, 55316917, 580962810935504541, 580921637792577515⟩,
⟨55316917, 55509343, 580921637792577515, 580808762184199668⟩,
⟨55509343, 55579061, 580808762184199668, 580767857237625032⟩
]⟩,
⟨55579061, 56627637, 580767857237625032, 580159332746586379, [
⟨55579061, 55772170, 580767857237625032, 580654022380133855⟩,
⟨55772170, 55841205, 580654022380133855, 580613830428572161⟩,
⟨55841205, 56034997, 580613830428572161, 580501607224140846⟩,
⟨56034997, 56103349, 580501607224140846, 580461479225722310⟩,
⟨56103349, 56297823, 580461479225722310, 580348413980311254⟩,
⟨56297823, 56365493, 580348413980311254, 580309513627705048⟩,
⟨56365493, 56560648, 580309513627705048, 580197837654776738⟩,
⟨56560648, 56627637, 580197837654776738, 580159332746586379⟩
]⟩,
⟨56627637, 57676213, 580159332746586379, 579562338587695737, [
⟨56627637, 56823472, 580159332746586379, 580045624234221389⟩,
⟨56823472, 56889781, 580045624234221389, 580008358002693794⟩,
⟨56889781, 57086296, 580008358002693794, 579896261192799120⟩,
⟨57086296, 57151925, 579896261192799120, 579858921843903009⟩,
⟨57151925, 57349119, 579858921843903009, 579746163854592130⟩,
⟨57349119, 57414069, 579746163854592130, 579709732357385371⟩,
⟨57414069, 57611941, 579709732357385371, 579598524519006085⟩,
⟨57611941, 57676213, 579598524519006085, 579562338587695737⟩
]⟩,
⟨57676213, 58724789, 579562338587695737, 578979291359167093, [
⟨57676213, 57874762, 579562338587695737, 579451714352777630⟩,
⟨57874762, 57938357, 579451714352777630, 579416111581692355⟩,
⟨57938357, 58137582, 579416111581692355, 579304707922737428⟩,
⟨58137582, 58200501, 579304707922737428, 579269932241141959⟩,
⟨58200501, 58400402, 579269932241141959, 579158491850559006⟩,
⟨58400402, 58462645, 579158491850559006, 579124485759809824⟩,
⟨58462645, 58663221, 579124485759809824, 579013018480335122⟩,
⟨58663221, 58724789, 579013018480335122, 578979291359167093⟩
]⟩
]

theorem c09 : RosserMediumSqrtChain.allGroups groups09 = true :=
  by decide +kernel

end RosserMediumSqrtCertificates

-- Source: Solutions/RosserMediumSqrtCertificates/C10.lean
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RosserMediumSqrtCertificates

def groups10 : List RosserMediumSqrtChain.Group := [
⟨58724789, 59773365, 578979291359167093, 578407543750526497, [
⟨58724789, 58926039, 578979291359167093, 578867679714886752⟩,
⟨58926039, 58986933, 578867679714886752, 578834945537520405⟩,
⟨58986933, 59188857, 578834945537520405, 578724513819576444⟩,
⟨59188857, 59249077, 578724513819576444, 578692098951680967⟩,
⟨59249077, 59451673, 578692098951680967, 578581968485516618⟩,
⟨59451673, 59511221, 578581968485516618, 578549597688637703⟩,
⟨59511221, 59714489, 578549597688637703, 578439318989131730⟩,
⟨59714489, 59773365, 578439318989131730, 578407543750526497⟩
]⟩,
⟨59773365, 60821941, 578407543750526497, 577845511261827933, [
⟨59773365, 59977304, 578407543750526497, 578297784082129285⟩,
⟨59977304, 60035509, 578297784082129285, 578266222784258318⟩,
⟨60035509, 60240119, 578266222784258318, 578156259327235659⟩,
⟨60240119, 60297653, 578156259327235659, 578125812089877045⟩,
⟨60297653, 60502932, 578125812089877045, 578015557474331821⟩,
⟨60502932, 60559797, 578015557474331821, 577985641243912156⟩,
⟨60559797, 60765745, 577985641243912156, 577875405142210471⟩,
⟨60765745, 60821941, 577875405142210471, 577845511261827933⟩
]⟩,
⟨60821941, 61870517, 577845511261827933, 577296361413735141, [
⟨60821941, 61028557, 577845511261827933, 577735700588484021⟩,
⟨61028557, 61084085, 577735700588484021, 577706642484020239⟩,
⟨61084085, 61291369, 577706642484020239, 577598273604790483⟩,
⟨61291369, 61346229, 577598273604790483, 577570034426922552⟩,
⟨61346229, 61554180, 577570034426922552, 577461128808542456⟩,
⟨61554180, 61608373, 577461128808542456, 577432988491431668⟩,
⟨61608373, 61816990, 577432988491431668, 577324450382216311⟩,
⟨61816990, 61870517, 577324450382216311, 577296361413735141⟩
]⟩,
⟨61870517, 62919093, 577296361413735141, 576755905413529995, [
⟨61870517, 62079800, 577296361413735141, 577187694028262425⟩,
⟨62079800, 62132661, 577187694028262425, 577159776869634990⟩,
⟨62132661, 62342608, 577159776869634990, 577051279035471160⟩,
⟨62342608, 62394805, 577051279035471160, 577024808806721497⟩,
⟨62394805, 62605416, 577024808806721497, 576916836207258551⟩,
⟨62605416, 62656949, 576916836207258551, 576890823920910700⟩,
⟨62656949, 62868224, 576890823920910700, 576781967965459285⟩,
⟨62868224, 62919093, 576781967965459285, 576755905413529995⟩
]⟩,
⟨62919093, 63967669, 576755905413529995, 576224620130078020, [
⟨62919093, 63131030, 576755905413529995, 576648251429060317⟩,
⟨63131030, 63181237, 576648251429060317, 576622841837254829⟩,
⟨63181237, 63393836, 576622841837254829, 576514693351986415⟩,
⟨63393836, 63443381, 576514693351986415, 576489449362716807⟩,
⟨63443381, 63656641, 576489449362716807, 576381863013264998⟩,
⟨63656641, 63705525, 576381863013264998, 576357271759428021⟩,
⟨63705525, 63919446, 576357271759428021, 576248915542264234⟩,
⟨63919446, 63967669, 576248915542264234, 576224620130078020⟩
]⟩,
⟨63967669, 65016245, 576224620130078020, 575705208530693782, [
⟨63967669, 64182250, 576224620130078020, 576117622556531228⟩,
⟨64182250, 64229813, 576117622556531228, 576093701085509279⟩,
⟨64229813, 64445053, 576093701085509279, 575986242202740260⟩,
⟨64445053, 64491957, 575986242202740260, 575963218763885405⟩,
⟨64491957, 64707855, 575963218763885405, 575856853636695672⟩,
⟨64707855, 64754101, 575856853636695672, 575834311209649910⟩,
⟨64754101, 64970657, 575834311209649910, 575727734621126970⟩,
⟨64970657, 65016245, 575727734621126970, 575705208530693782⟩
]⟩,
⟨65016245, 66064821, 575705208530693782, 575193090011834115, [
⟨65016245, 65233458, 575705208530693782, 575598801613075762⟩,
⟨65233458, 65278389, 575598801613075762, 575576953340696851⟩,
⟨65278389, 65496259, 575576953340696851, 575469440433103821⟩,
⟨65496259, 65540533, 575469440433103821, 575448132456582927⟩,
⟨65540533, 65759059, 575448132456582927, 575342413563881948⟩,
⟨65759059, 65802677, 575342413563881948, 575321265273903993⟩,
⟨65802677, 66021858, 575321265273903993, 575214306258898051⟩,
⟨66021858, 66064821, 575214306258898051, 575193090011834115⟩
]⟩,
⟨66064821, 67113397, 575193090011834115, 574689859820943419, [
⟨66064821, 66284656, 575193090011834115, 575086952941856797⟩,
⟨66284656, 66326965, 575086952941856797, 575066059492925734⟩,
⟨66326965, 66547454, 575066059492925734, 574959923261883686⟩,
⟨66547454, 66589109, 574959923261883686, 574940127319020270⟩,
⟨66589109, 66810252, 574940127319020270, 574834207123427593⟩,
⟨66810252, 66851253, 574834207123427593, 574814845842570027⟩,
⟨66851253, 67073048, 574814845842570027, 574709295327618668⟩,
⟨67073048, 67113397, 574709295327618668, 574689859820943419⟩
]⟩
]

theorem c10 : RosserMediumSqrtChain.allGroups groups10 = true :=
  by decide +kernel

end RosserMediumSqrtCertificates

-- Source: Solutions/RosserMediumSqrtCertificates/C11.lean
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RosserMediumSqrtCertificates

def groups11 : List RosserMediumSqrtChain.Group := [
⟨67113397, 68161973, 574689859820943419, 574195311614942326, [
⟨67113397, 67335844, 574689859820943419, 574583865691441062⟩,
⟨67335844, 67375541, 574583865691441062, 574565457017642837⟩,
⟨67375541, 67598639, 574565457017642837, 574459309259245801⟩,
⟨67598639, 67637685, 574459309259245801, 574441349802379291⟩,
⟨67637685, 67861434, 574441349802379291, 574335898731930999⟩,
⟨67861434, 67899829, 574335898731930999, 574318020998814569⟩,
⟨67899829, 68124228, 574318020998814569, 574212847062666780⟩,
⟨68124228, 68161973, 574212847062666780, 574195311614942326⟩
]⟩,
⟨68161973, 69210549, 574195311614942326, 573710643470399151, [
⟨68161973, 68387022, 574195311614942326, 574090757679821584⟩,
⟨68387022, 68424117, 574090757679821584, 574073301601739190⟩,
⟨68424117, 68649815, 574073301601739190, 573968835463771140⟩,
⟨68649815, 68686261, 573968835463771140, 573951792488426073⟩,
⟨68686261, 68912607, 573951792488426073, 573847538753775824⟩,
⟨68912607, 68948405, 573847538753775824, 573831230260708193⟩,
⟨68948405, 69175398, 573831230260708193, 573726604736658734⟩,
⟨69175398, 69210549, 573726604736658734, 573710643470399151⟩
]⟩,
⟨69210549, 70259125, 573710643470399151, 573232682901911816, [
⟨69210549, 69438189, 573710643470399151, 573605998779908221⟩,
⟨69438189, 69472693, 573605998779908221, 573589993778955533⟩,
⟨69472693, 69700980, 573589993778955533, 573485377610928618⟩,
⟨69700980, 69734837, 573485377610928618, 573469979101969676⟩,
⟨69734837, 69963770, 573469979101969676, 573366220340707048⟩,
⟨69963770, 69996981, 573366220340707048, 573351415371664967⟩,
⟨69996981, 70226559, 573351415371664967, 573247723337717540⟩,
⟨70226559, 70259125, 573247723337717540, 573232682901911816⟩
]⟩,
⟨70259125, 71307701, 573232682901911816, 572763286266611996, [
⟨70259125, 70489347, 573232682901911816, 573128340794642068⟩,
⟨70489347, 70521269, 573128340794642068, 573114009741158059⟩,
⟨70521269, 70752135, 573114009741158059, 573010595783082594⟩,
⟨70752135, 70783413, 573010595783082594, 572997025269409213⟩,
⟨70783413, 71014923, 572997025269409213, 572893595117360093⟩,
⟨71014923, 71045557, 572893595117360093, 572880238761192684⟩,
⟨71045557, 71277709, 572880238761192684, 572776502286873657⟩,
⟨71277709, 71307701, 572776502286873657, 572763286266611996⟩
]⟩,
⟨71307701, 72356277, 572763286266611996, 572300102654232814, [
⟨71307701, 71540495, 572763286266611996, 572659623485996261⟩,
⟨71540495, 71569845, 572659623485996261, 572646466599604200⟩,
⟨71569845, 71803281, 572646466599604200, 572544050170791598⟩,
⟨71803281, 71831989, 572544050170791598, 572531406403267104⟩,
⟨71831989, 72066066, 572531406403267104, 572428350356250622⟩,
⟨72066066, 72094133, 572428350356250622, 572415683722022206⟩,
⟨72094133, 72328850, 572415683722022206, 572311977173239706⟩,
⟨72328850, 72356277, 572311977173239706, 572300102654232814⟩
]⟩,
⟨72356277, 73404853, 572300102654232814, 571845823191513173, [
⟨72356277, 72591634, 572300102654232814, 572197581848282617⟩,
⟨72591634, 72618421, 572197581848282617, 572186052124131689⟩,
⟨72618421, 72854417, 572186052124131689, 572083316606855679⟩,
⟨72854417, 72880565, 572083316606855679, 572072074089568385⟩,
⟨72880565, 73117200, 572072074089568385, 571969476665090737⟩,
⟨73117200, 73142709, 571969476665090737, 571958589562708658⟩,
⟨73142709, 73379982, 571958589562708658, 571856560178647292⟩,
⟨73379982, 73404853, 571856560178647292, 571845823191513173⟩
]⟩,
⟨73404853, 74453429, 571845823191513173, 571398902870036566, [
⟨73404853, 73642764, 571845823191513173, 571743626173414122⟩,
⟨73642764, 73666997, 571743626173414122, 571733216808079048⟩,
⟨73666997, 73905545, 571733216808079048, 571631100439694968⟩,
⟨73905545, 73929141, 571631100439694968, 571620853790264022⟩,
⟨73929141, 74168325, 571620853790264022, 571520083994074916⟩,
⟨74168325, 74191285, 571520083994074916, 571510176039174495⟩,
⟨74191285, 74431105, 571510176039174495, 571408505302937530⟩,
⟨74431105, 74453429, 571408505302937530, 571398902870036566⟩
]⟩,
⟨74453429, 75502005, 571398902870036566, 570957736512577618, [
⟨74453429, 74693884, 571398902870036566, 571297709409138983⟩,
⟨74693884, 74715573, 571297709409138983, 571288601398385854⟩,
⟨74715573, 74956663, 571288601398385854, 571186690426996212⟩,
⟨74956663, 74977717, 571186690426996212, 571177981798675423⟩,
⟨74977717, 75219441, 571177981798675423, 571076204498796539⟩,
⟨75219441, 75239861, 571076204498796539, 571067725306833404⟩,
⟨75239861, 75482218, 571067725306833404, 570966116523003151⟩,
⟨75482218, 75502005, 570966116523003151, 570957736512577618⟩
]⟩
]

theorem c11 : RosserMediumSqrtChain.allGroups groups11 = true :=
  by decide +kernel

end RosserMediumSqrtCertificates

-- Source: Solutions/RosserMediumSqrtCertificates/C12.lean
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RosserMediumSqrtCertificates

def groups12 : List RosserMediumSqrtChain.Group := [
⟨75502005, 76550581, 570957736512577618, 570524278825427456, [
⟨75502005, 75744995, 570957736512577618, 570857050925812240⟩,
⟨75744995, 75764149, 570857050925812240, 570848806995105001⟩,
⟨75764149, 75885960, 570848806995105001, 570797991889553637⟩,
⟨75885960, 76026293, 570797991889553637, 570739431786288673⟩,
⟨76026293, 76270548, 570739431786288673, 570639081209794733⟩,
⟨76270548, 76288437, 570639081209794733, 570631877146022259⟩,
⟨76288437, 76533323, 570631877146022259, 570531568645926931⟩,
⟨76533323, 76550581, 570531568645926931, 570524278825427456⟩
]⟩,
⟨76550581, 77599157, 570524278825427456, 570097452389675669, [
⟨76550581, 76796098, 570524278825427456, 570424340514297093⟩,
⟨76796098, 76812725, 570424340514297093, 570417634005580868⟩,
⟨76812725, 77058872, 570417634005580868, 570316646416817187⟩,
⟨77058872, 77074869, 570316646416817187, 570310171215899380⟩,
⟨77074869, 77321646, 570310171215899380, 570209922308625791⟩,
⟨77321646, 77337013, 570209922308625791, 570203654624692257⟩,
⟨77337013, 77584419, 570203654624692257, 570103558121753423⟩,
⟨77584419, 77599157, 570103558121753423, 570097452389675669⟩
]⟩,
⟨77599157, 78647733, 570097452389675669, 569677510248247462, [
⟨77599157, 77847192, 570097452389675669, 569997815541159982⟩,
⟨77847192, 77861301, 569997815541159982, 569991877972499299⟩,
⟨77861301, 78109964, 569991877972499299, 569891703106880043⟩,
⟨78109964, 78123445, 569891703106880043, 569886173235749855⟩,
⟨78123445, 78372736, 569886173235749855, 569786935321125622⟩,
⟨78372736, 78385589, 569786935321125622, 569781737565124029⟩,
⟨78385589, 78635507, 569781737565124029, 569682247821178615⟩,
⟨78635507, 78647733, 569682247821178615, 569677510248247462⟩
]⟩,
⟨78647733, 79696309, 569677510248247462, 569262871994210482, [
⟨78647733, 78898278, 569677510248247462, 569577740041299645⟩,
⟨78898278, 78909877, 569577740041299645, 569573206773903091⟩,
⟨78909877, 79161048, 569573206773903091, 569473699944007237⟩,
⟨79161048, 79172021, 569473699944007237, 569469204109690968⟩,
⟨79172021, 79423817, 569469204109690968, 569369908896114171⟩,
⟨79423817, 79434165, 569369908896114171, 569365672445949504⟩,
⟨79434165, 79686586, 569365672445949504, 569266493676572368⟩,
⟨79686586, 79696309, 569266493676572368, 569262871994210482⟩
]⟩,
⟨79696309, 80744885, 569262871994210482, 568854342139216905, [
⟨79696309, 79949355, 569262871994210482, 569163765582606402⟩,
⟨79949355, 79958453, 569163765582606402, 569159971353111263⟩,
⟨79958453, 80212123, 569159971353111263, 569061641784722866⟩,
⟨80212123, 80220597, 569061641784722866, 569058449458711872⟩,
⟨80220597, 80474890, 569058449458711872, 568958772302503337⟩,
⟨80474890, 80482741, 568958772302503337, 568955718213338817⟩,
⟨80482741, 80737657, 568955718213338817, 568857216669317190⟩,
⟨80737657, 80744885, 568857216669317190, 568854342139216905⟩
]⟩,
⟨80744885, 81793461, 568854342139216905, 568450432387311690, [
⟨80744885, 81000424, 568854342139216905, 568755017050531204⟩,
⟨81000424, 81007029, 568755017050531204, 568752370011854660⟩,
⟨81007029, 81263190, 568752370011854660, 568652962999589664⟩,
⟨81263190, 81269173, 568652962999589664, 568650611871578576⟩,
⟨81269173, 81525955, 568650611871578576, 568552305323329566⟩,
⟨81525955, 81531317, 568552305323329566, 568550324810806567⟩,
⟨81531317, 81788720, 568550324810806567, 568452135147762519⟩,
⟨81788720, 81793461, 568452135147762519, 568450432387311690⟩
]⟩,
⟨81793461, 82842037, 568450432387311690, 568052916627623988, [
⟨81793461, 82051485, 568450432387311690, 568351742232671569⟩,
⟨82051485, 82055605, 568351742232671569, 568350176823957254⟩,
⟨82055605, 82314248, 568350176823957254, 568252675905734997⟩,
⟨82314248, 82317749, 568252675905734997, 568251267633074762⟩,
⟨82317749, 82577012, 568251267633074762, 568153157513399442⟩,
⟨82577012, 82579893, 568153157513399442, 568152077329059728⟩,
⟨82579893, 82839775, 568152077329059728, 568053773773424390⟩,
⟨82839775, 82842037, 568053773773424390, 568052916627623988⟩
]⟩,
⟨82842037, 83890613, 568052916627623988, 567661696964059516, [
⟨82842037, 83102537, 568052916627623988, 567955145537588495⟩,
⟨83102537, 83104181, 567955145537588495, 567954509946089543⟩,
⟨83104181, 83365299, 567954509946089543, 567857590010795534⟩,
⟨83365299, 83366325, 567857590010795534, 567857133631039369⟩,
⟨83366325, 83628061, 567857133631039369, 567759351769431536⟩,
⟨83628061, 83628469, 567759351769431536, 567759182042403443⟩,
⟨83628469, 83890613, 567759182042403443, 567661696964059516⟩
]⟩
]

theorem c12 : RosserMediumSqrtChain.allGroups groups12 = true :=
  by decide +kernel

end RosserMediumSqrtCertificates

-- Source: Solutions/RosserMediumSqrtCertificates/C13.lean
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RosserMediumSqrtCertificates

def groups13 : List RosserMediumSqrtChain.Group := [
⟨83890613, 84939189, 567661696964059516, 567276308620579955, [
⟨83890613, 84152757, 567661696964059516, 567564531036700663⟩,
⟨84152757, 84414901, 567564531036700663, 567468331381403947⟩,
⟨84414901, 84677045, 567468331381403947, 567372076037482146⟩,
⟨84677045, 84939189, 567372076037482146, 567276308620579955⟩
]⟩,
⟨84939189, 85987765, 567276308620579955, 566895239405269343, [
⟨84939189, 85201333, 567276308620579955, 567180812892573256⟩,
⟨85201333, 85463477, 567180812892573256, 567085081904665577⟩,
⟨85463477, 85725621, 567085081904665577, 566990334886468725⟩,
⟨85725621, 85987765, 566990334886468725, 566895239405269343⟩
]⟩,
⟨85987765, 87036341, 566895239405269343, 566519354377793871, [
⟨85987765, 86249909, 566895239405269343, 566801035188696796⟩,
⟨86249909, 86512053, 566801035188696796, 566706634372567575⟩,
⟨86512053, 86774197, 566706634372567575, 566612985521398521⟩,
⟨86774197, 87036341, 566612985521398521, 566519354377793871⟩
]⟩,
⟨87036341, 88084917, 566519354377793871, 566148496928795172, [
⟨87036341, 87298485, 566519354377793871, 566426176439232491⟩,
⟨87298485, 87560629, 566426176439232491, 566333720907551145⟩,
⟨87560629, 87822773, 566333720907551145, 566241472274216909⟩,
⟨87822773, 88084917, 566241472274216909, 566148496928795172⟩
]⟩,
⟨88084917, 89133493, 566148496928795172, 565782613891760354, [
⟨88084917, 88347061, 566148496928795172, 566056236512843801⟩,
⟨88347061, 88609205, 566056236512843801, 565965357819095019⟩,
⟨88609205, 88871349, 565965357819095019, 565873672037956971⟩,
⟨88871349, 89133493, 565873672037956971, 565782613891760354⟩
]⟩,
⟨89133493, 90182069, 565782613891760354, 565421925066953927, [
⟨89133493, 89395637, 565782613891760354, 565691792912144812⟩,
⟨89395637, 89657781, 565691792912144812, 565601890934863582⟩,
⟨89657781, 89919925, 565601890934863582, 565512128116425964⟩,
⟨89919925, 90182069, 565512128116425964, 565421925066953927⟩
]⟩,
⟨90182069, 91230645, 565421925066953927, 565064920508081792, [
⟨90182069, 90444213, 565421925066953927, 565332316432480672⟩,
⟨90444213, 90706357, 565332316432480672, 565242968575930911⟩,
⟨90706357, 90968501, 565242968575930911, 565153600935417013⟩,
⟨90968501, 91230645, 565153600935417013, 565064920508081792⟩
]⟩,
⟨91230645, 92279221, 565064920508081792, 564713089500303654, [
⟨91230645, 91492789, 565064920508081792, 564976470260700640⟩,
⟨91492789, 91754933, 564976470260700640, 564888059288891430⟩,
⟨91754933, 92017077, 564888059288891430, 564800553844656152⟩,
⟨92017077, 92279221, 564800553844656152, 564713089500303654⟩
]⟩
]

theorem c13 : RosserMediumSqrtChain.allGroups groups13 = true :=
  by decide +kernel

end RosserMediumSqrtCertificates

-- Source: Solutions/RosserMediumSqrtCertificates/C14.lean
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RosserMediumSqrtCertificates

def groups14 : List RosserMediumSqrtChain.Group := [
⟨92279221, 93327797, 564713089500303654, 564365850923681747, [
⟨92279221, 92541365, 564713089500303654, 564625887086409811⟩,
⟨92541365, 92803509, 564625887086409811, 564538603536861858⟩,
⟨92803509, 93065653, 564538603536861858, 564452350345575944⟩,
⟨93065653, 93327797, 564452350345575944, 564365850923681747⟩
]⟩,
⟨93327797, 94376373, 564365850923681747, 564022426187831760, [
⟨93327797, 93589941, 564365850923681747, 564279456083644121⟩,
⟨93589941, 93852085, 564279456083644121, 564193894510095023⟩,
⟨93852085, 94114229, 564193894510095023, 564107396039305398⟩,
⟨94114229, 94376373, 564107396039305398, 564022426187831760⟩
]⟩,
⟨94376373, 95424949, 564022426187831760, 563682455421115701, [
⟨94376373, 94638517, 564022426187831760, 563937173422006777⟩,
⟨94638517, 94900661, 563937173422006777, 563851711627849912⟩,
⟨94900661, 95162805, 563851711627849912, 563767007718330474⟩,
⟨95162805, 95424949, 563767007718330474, 563682455421115701⟩
]⟩,
⟨95424949, 96473525, 563682455421115701, 563347592713998754, [
⟨95424949, 95687093, 563682455421115701, 563598164968083189⟩,
⟨95687093, 95949237, 563598164968083189, 563514377238074903⟩,
⟨95949237, 96211381, 563514377238074903, 563430923452476763⟩,
⟨96211381, 96473525, 563430923452476763, 563347592713998754⟩
]⟩,
⟨96473525, 97522101, 563347592713998754, 563016187889385014, [
⟨96473525, 96735669, 563347592713998754, 563264249676447599⟩,
⟨96735669, 96997813, 563264249676447599, 563181202632345939⟩,
⟨96997813, 97259957, 563181202632345939, 563099000373048386⟩,
⟨97259957, 97522101, 563099000373048386, 563016187889385014⟩
]⟩,
⟨97522101, 98570677, 563016187889385014, 562688684888144126, [
⟨97522101, 97784245, 563016187889385014, 562933741636562887⟩,
⟨97784245, 98046389, 562933741636562887, 562852033742582020⟩,
⟨98046389, 98308533, 562852033742582020, 562770464866682660⟩,
⟨98308533, 98570677, 562770464866682660, 562688684888144126⟩
]⟩,
⟨98570677, 99619253, 562688684888144126, 562366105497831683, [
⟨98570677, 98832821, 562688684888144126, 562608091141154160⟩,
⟨98832821, 99094965, 562608091141154160, 562527228465371674⟩,
⟨99094965, 99357109, 562527228465371674, 562447078321141721⟩,
⟨99357109, 99619253, 562447078321141721, 562366105497831683⟩
]⟩,
⟨99619253, 100000000, 562366105497831683, 562249863732463535, [
⟨99619253, 99881397, 562366105497831683, 562286230301391113⟩,
⟨99881397, 100000000, 562286230301391113, 562249863732463535⟩
]⟩
]

theorem c14 : RosserMediumSqrtChain.allGroups groups14 = true :=
  by decide +kernel

end RosserMediumSqrtCertificates

-- Source: Solutions/RosserMediumSqrtFull.lean
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RosserMediumSqrtCertificate

def certifiedGroups : List RosserMediumSqrtChain.Group :=
  RosserMediumSqrtCertificates.groups00 ++
  RosserMediumSqrtCertificates.groups01 ++
  RosserMediumSqrtCertificates.groups02 ++
  RosserMediumSqrtCertificates.groups03 ++
  RosserMediumSqrtCertificates.groups04 ++
  RosserMediumSqrtCertificates.groups05 ++
  RosserMediumSqrtCertificates.groups06 ++
  RosserMediumSqrtCertificates.groups07 ++
  RosserMediumSqrtCertificates.groups08 ++
  RosserMediumSqrtCertificates.groups09 ++
  RosserMediumSqrtCertificates.groups10 ++
  RosserMediumSqrtCertificates.groups11 ++
  RosserMediumSqrtCertificates.groups12 ++
  RosserMediumSqrtCertificates.groups13 ++
  RosserMediumSqrtCertificates.groups14

theorem all_checks : RosserMediumSqrtChain.allGroups certifiedGroups = true :=
  RosserMediumSqrtChain.allGroups_append_true (xs := RosserMediumSqrtCertificates.groups00) (ys := RosserMediumSqrtCertificates.groups01 ++ RosserMediumSqrtCertificates.groups02 ++ RosserMediumSqrtCertificates.groups03 ++ RosserMediumSqrtCertificates.groups04 ++ RosserMediumSqrtCertificates.groups05 ++ RosserMediumSqrtCertificates.groups06 ++ RosserMediumSqrtCertificates.groups07 ++ RosserMediumSqrtCertificates.groups08 ++ RosserMediumSqrtCertificates.groups09 ++ RosserMediumSqrtCertificates.groups10 ++ RosserMediumSqrtCertificates.groups11 ++ RosserMediumSqrtCertificates.groups12 ++ RosserMediumSqrtCertificates.groups13 ++ RosserMediumSqrtCertificates.groups14) RosserMediumSqrtCertificates.c00 (RosserMediumSqrtChain.allGroups_append_true (xs := RosserMediumSqrtCertificates.groups01) (ys := RosserMediumSqrtCertificates.groups02 ++ RosserMediumSqrtCertificates.groups03 ++ RosserMediumSqrtCertificates.groups04 ++ RosserMediumSqrtCertificates.groups05 ++ RosserMediumSqrtCertificates.groups06 ++ RosserMediumSqrtCertificates.groups07 ++ RosserMediumSqrtCertificates.groups08 ++ RosserMediumSqrtCertificates.groups09 ++ RosserMediumSqrtCertificates.groups10 ++ RosserMediumSqrtCertificates.groups11 ++ RosserMediumSqrtCertificates.groups12 ++ RosserMediumSqrtCertificates.groups13 ++ RosserMediumSqrtCertificates.groups14) RosserMediumSqrtCertificates.c01 (RosserMediumSqrtChain.allGroups_append_true (xs := RosserMediumSqrtCertificates.groups02) (ys := RosserMediumSqrtCertificates.groups03 ++ RosserMediumSqrtCertificates.groups04 ++ RosserMediumSqrtCertificates.groups05 ++ RosserMediumSqrtCertificates.groups06 ++ RosserMediumSqrtCertificates.groups07 ++ RosserMediumSqrtCertificates.groups08 ++ RosserMediumSqrtCertificates.groups09 ++ RosserMediumSqrtCertificates.groups10 ++ RosserMediumSqrtCertificates.groups11 ++ RosserMediumSqrtCertificates.groups12 ++ RosserMediumSqrtCertificates.groups13 ++ RosserMediumSqrtCertificates.groups14) RosserMediumSqrtCertificates.c02 (RosserMediumSqrtChain.allGroups_append_true (xs := RosserMediumSqrtCertificates.groups03) (ys := RosserMediumSqrtCertificates.groups04 ++ RosserMediumSqrtCertificates.groups05 ++ RosserMediumSqrtCertificates.groups06 ++ RosserMediumSqrtCertificates.groups07 ++ RosserMediumSqrtCertificates.groups08 ++ RosserMediumSqrtCertificates.groups09 ++ RosserMediumSqrtCertificates.groups10 ++ RosserMediumSqrtCertificates.groups11 ++ RosserMediumSqrtCertificates.groups12 ++ RosserMediumSqrtCertificates.groups13 ++ RosserMediumSqrtCertificates.groups14) RosserMediumSqrtCertificates.c03 (RosserMediumSqrtChain.allGroups_append_true (xs := RosserMediumSqrtCertificates.groups04) (ys := RosserMediumSqrtCertificates.groups05 ++ RosserMediumSqrtCertificates.groups06 ++ RosserMediumSqrtCertificates.groups07 ++ RosserMediumSqrtCertificates.groups08 ++ RosserMediumSqrtCertificates.groups09 ++ RosserMediumSqrtCertificates.groups10 ++ RosserMediumSqrtCertificates.groups11 ++ RosserMediumSqrtCertificates.groups12 ++ RosserMediumSqrtCertificates.groups13 ++ RosserMediumSqrtCertificates.groups14) RosserMediumSqrtCertificates.c04 (RosserMediumSqrtChain.allGroups_append_true (xs := RosserMediumSqrtCertificates.groups05) (ys := RosserMediumSqrtCertificates.groups06 ++ RosserMediumSqrtCertificates.groups07 ++ RosserMediumSqrtCertificates.groups08 ++ RosserMediumSqrtCertificates.groups09 ++ RosserMediumSqrtCertificates.groups10 ++ RosserMediumSqrtCertificates.groups11 ++ RosserMediumSqrtCertificates.groups12 ++ RosserMediumSqrtCertificates.groups13 ++ RosserMediumSqrtCertificates.groups14) RosserMediumSqrtCertificates.c05 (RosserMediumSqrtChain.allGroups_append_true (xs := RosserMediumSqrtCertificates.groups06) (ys := RosserMediumSqrtCertificates.groups07 ++ RosserMediumSqrtCertificates.groups08 ++ RosserMediumSqrtCertificates.groups09 ++ RosserMediumSqrtCertificates.groups10 ++ RosserMediumSqrtCertificates.groups11 ++ RosserMediumSqrtCertificates.groups12 ++ RosserMediumSqrtCertificates.groups13 ++ RosserMediumSqrtCertificates.groups14) RosserMediumSqrtCertificates.c06 (RosserMediumSqrtChain.allGroups_append_true (xs := RosserMediumSqrtCertificates.groups07) (ys := RosserMediumSqrtCertificates.groups08 ++ RosserMediumSqrtCertificates.groups09 ++ RosserMediumSqrtCertificates.groups10 ++ RosserMediumSqrtCertificates.groups11 ++ RosserMediumSqrtCertificates.groups12 ++ RosserMediumSqrtCertificates.groups13 ++ RosserMediumSqrtCertificates.groups14) RosserMediumSqrtCertificates.c07 (RosserMediumSqrtChain.allGroups_append_true (xs := RosserMediumSqrtCertificates.groups08) (ys := RosserMediumSqrtCertificates.groups09 ++ RosserMediumSqrtCertificates.groups10 ++ RosserMediumSqrtCertificates.groups11 ++ RosserMediumSqrtCertificates.groups12 ++ RosserMediumSqrtCertificates.groups13 ++ RosserMediumSqrtCertificates.groups14) RosserMediumSqrtCertificates.c08 (RosserMediumSqrtChain.allGroups_append_true (xs := RosserMediumSqrtCertificates.groups09) (ys := RosserMediumSqrtCertificates.groups10 ++ RosserMediumSqrtCertificates.groups11 ++ RosserMediumSqrtCertificates.groups12 ++ RosserMediumSqrtCertificates.groups13 ++ RosserMediumSqrtCertificates.groups14) RosserMediumSqrtCertificates.c09 (RosserMediumSqrtChain.allGroups_append_true (xs := RosserMediumSqrtCertificates.groups10) (ys := RosserMediumSqrtCertificates.groups11 ++ RosserMediumSqrtCertificates.groups12 ++ RosserMediumSqrtCertificates.groups13 ++ RosserMediumSqrtCertificates.groups14) RosserMediumSqrtCertificates.c10 (RosserMediumSqrtChain.allGroups_append_true (xs := RosserMediumSqrtCertificates.groups11) (ys := RosserMediumSqrtCertificates.groups12 ++ RosserMediumSqrtCertificates.groups13 ++ RosserMediumSqrtCertificates.groups14) RosserMediumSqrtCertificates.c11 (RosserMediumSqrtChain.allGroups_append_true (xs := RosserMediumSqrtCertificates.groups12) (ys := RosserMediumSqrtCertificates.groups13 ++ RosserMediumSqrtCertificates.groups14) RosserMediumSqrtCertificates.c12 (RosserMediumSqrtChain.allGroups_append_true (xs := RosserMediumSqrtCertificates.groups13) (ys := RosserMediumSqrtCertificates.groups14) RosserMediumSqrtCertificates.c13 (RosserMediumSqrtCertificates.c14))))))))))))))

theorem all_links : RosserMediumSqrtChain.linkedGroups 4533 1227903923884082104
    100000000 certifiedGroups = true := by
  decide +kernel

theorem product_bound_4500_to_1e8 (x : ℝ) (hx : 4500 ≤ x) (hx' : x ≤ 10 ^ 8) :
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) <
      Real.exp Real.eulerMascheroniConstant * Real.log x +
        2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x := by
  by_cases hlo : x ≤ 4533
  · exact RosserProductCertificate.product_bound_4500_to_4533 x hx hlo
  have hstart : (1227903923884082104 : ℝ) / RosserLogCertificate.scale ≤
      RosserMomentBridge.reciprocalProduct 4533 := by
    simpa only [RosserLogCertificate.scale, Nat.cast_pow, Nat.cast_ofNat,
      RosserMomentBridge.reciprocalProduct] using RosserProductCertificate.reciprocal_4533_lower
  have htop : x ≤ (100000000 : ℝ) := by norm_num at hx'; exact hx'
  exact RosserMediumSqrtChain.allGroups_sound certifiedGroups 4533
    1227903923884082104 100000000 hstart
    (RosserMediumSqrtChain.linkedGroups_sound _ _ _ _ all_links)
    all_checks x (lt_of_not_ge hlo) htop

#print axioms product_bound_4500_to_1e8
end RosserMediumSqrtCertificate

theorem solution (x : ℝ) (hx : 4500 ≤ x) (hx' : x ≤ 10 ^ 8) :
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) <
      Real.exp Real.eulerMascheroniConstant * Real.log x +
        2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x :=
  RosserMediumSqrtCertificate.product_bound_4500_to_1e8 x hx hx'

#print axioms solution
