-- Prove2me | solution 1 for TaoFivePrimes.rosser_psi_certificate_55574528_to_100000000
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-24T00:57:25.998493+00:00
-- url     : https://prove2.me/submissions/ea1e3c7f-6050-4e18-a10c-d5c70c339200

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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic
import Theorems.Thm_TaoFivePrimes_rosser_psi_certificate_13631488_to_55574528

namespace OddGoldbachPsiRangeThree

/-!
Finite Rosser--Schoenfeld psi certificate infrastructure.
The reusable bit-sieve and packed-moment proofs below are adapted from the
accepted Prove2Me submission 891aecdd-2026-4fbb-9bf7-a2b4a368f347 by sometik179.
The psi reduction, logarithm upper bounds, certificate composition, and
numerical data are supplied here. All numerical claims are kernel-checked.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace OddGoldbachWideAccepted
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

namespace RosserBitMoments

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

end RosserBitMoments


namespace RosserScan

/-- Force a natural-number state before the next recursive call. This avoids
re-evaluating a growing expression during kernel reduction. -/
def forceNat {α : Type} (n : ℕ) (f : ℕ → α) : α :=
  match n with
  | 0 => f 0
  | n + 1 => f (n + 1)


end RosserScan


namespace RosserSieveData

def divisors : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999, 2003, 2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143, 2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647, 2657, 2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731, 2741, 2749, 2753, 2767, 2777, 2789, 2791, 2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861, 2879, 2887, 2897, 2903, 2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971, 2999, 3001, 3011, 3019, 3023, 3037, 3041, 3049, 3061, 3067, 3079, 3083, 3089, 3109, 3119, 3121, 3137, 3163, 3167, 3169, 3181, 3187, 3191, 3203, 3209, 3217, 3221, 3229, 3251, 3253, 3257, 3259, 3271, 3299, 3301, 3307, 3313, 3319, 3323, 3329, 3331, 3343, 3347, 3359, 3361, 3371, 3373, 3389, 3391, 3407, 3413, 3433, 3449, 3457, 3461, 3463, 3467, 3469, 3491, 3499, 3511, 3517, 3527, 3529, 3533, 3539, 3541, 3547, 3557, 3559, 3571, 3581, 3583, 3593, 3607, 3613, 3617, 3623, 3631, 3637, 3643, 3659, 3671, 3673, 3677, 3691, 3697, 3701, 3709, 3719, 3727, 3733, 3739, 3761, 3767, 3769, 3779, 3793, 3797, 3803, 3821, 3823, 3833, 3847, 3851, 3853, 3863, 3877, 3881, 3889, 3907, 3911, 3917, 3919, 3923, 3929, 3931, 3943, 3947, 3967, 3989, 4001, 4003, 4007, 4013, 4019, 4021, 4027, 4049, 4051, 4057, 4073, 4079, 4091, 4093, 4099, 4111, 4127, 4129, 4133, 4139, 4153, 4157, 4159, 4177, 4201, 4211, 4217, 4219, 4229, 4231, 4241, 4243, 4253, 4259, 4261, 4271, 4273, 4283, 4289, 4297, 4327, 4337, 4339, 4349, 4357, 4363, 4373, 4391, 4397, 4409, 4421, 4423, 4441, 4447, 4451, 4457, 4463, 4481, 4483, 4493, 4507, 4513, 4517, 4519, 4523, 4547, 4549, 4561, 4567, 4583, 4591, 4597, 4603, 4621, 4637, 4639, 4643, 4649, 4651, 4657, 4663, 4673, 4679, 4691, 4703, 4721, 4723, 4729, 4733, 4751, 4759, 4783, 4787, 4789, 4793, 4799, 4801, 4813, 4817, 4831, 4861, 4871, 4877, 4889, 4903, 4909, 4919, 4931, 4933, 4937, 4943, 4951, 4957, 4967, 4969, 4973, 4987, 4993, 4999, 5003, 5009, 5011, 5021, 5023, 5039, 5051, 5059, 5077, 5081, 5087, 5099, 5101, 5107, 5113, 5119, 5147, 5153, 5167, 5171, 5179, 5189, 5197, 5209, 5227, 5231, 5233, 5237, 5261, 5273, 5279, 5281, 5297, 5303, 5309, 5323, 5333, 5347, 5351, 5381, 5387, 5393, 5399, 5407, 5413, 5417, 5419, 5431, 5437, 5441, 5443, 5449, 5471, 5477, 5479, 5483, 5501, 5503, 5507, 5519, 5521, 5527, 5531, 5557, 5563, 5569, 5573, 5581, 5591, 5623, 5639, 5641, 5647, 5651, 5653, 5657, 5659, 5669, 5683, 5689, 5693, 5701, 5711, 5717, 5737, 5741, 5743, 5749, 5779, 5783, 5791, 5801, 5807, 5813, 5821, 5827, 5839, 5843, 5849, 5851, 5857, 5861, 5867, 5869, 5879, 5881, 5897, 5903, 5923, 5927, 5939, 5953, 5981, 5987, 6007, 6011, 6029, 6037, 6043, 6047, 6053, 6067, 6073, 6079, 6089, 6091, 6101, 6113, 6121, 6131, 6133, 6143, 6151, 6163, 6173, 6197, 6199, 6203, 6211, 6217, 6221, 6229, 6247, 6257, 6263, 6269, 6271, 6277, 6287, 6299, 6301, 6311, 6317, 6323, 6329, 6337, 6343, 6353, 6359, 6361, 6367, 6373, 6379, 6389, 6397, 6421, 6427, 6449, 6451, 6469, 6473, 6481, 6491, 6521, 6529, 6547, 6551, 6553, 6563, 6569, 6571, 6577, 6581, 6599, 6607, 6619, 6637, 6653, 6659, 6661, 6673, 6679, 6689, 6691, 6701, 6703, 6709, 6719, 6733, 6737, 6761, 6763, 6779, 6781, 6791, 6793, 6803, 6823, 6827, 6829, 6833, 6841, 6857, 6863, 6869, 6871, 6883, 6899, 6907, 6911, 6917, 6947, 6949, 6959, 6961, 6967, 6971, 6977, 6983, 6991, 6997, 7001, 7013, 7019, 7027, 7039, 7043, 7057, 7069, 7079, 7103, 7109, 7121, 7127, 7129, 7151, 7159, 7177, 7187, 7193, 7207, 7211, 7213, 7219, 7229, 7237, 7243, 7247, 7253, 7283, 7297, 7307, 7309, 7321, 7331, 7333, 7349, 7351, 7369, 7393, 7411, 7417, 7433, 7451, 7457, 7459, 7477, 7481, 7487, 7489, 7499, 7507, 7517, 7523, 7529, 7537, 7541, 7547, 7549, 7559, 7561, 7573, 7577, 7583, 7589, 7591, 7603, 7607, 7621, 7639, 7643, 7649, 7669, 7673, 7681, 7687, 7691, 7699, 7703, 7717, 7723, 7727, 7741, 7753, 7757, 7759, 7789, 7793, 7817, 7823, 7829, 7841, 7853, 7867, 7873, 7877, 7879, 7883, 7901, 7907, 7919, 7927, 7933, 7937, 7949, 7951, 7963, 7993, 8009, 8011, 8017, 8039, 8053, 8059, 8069, 8081, 8087, 8089, 8093, 8101, 8111, 8117, 8123, 8147, 8161, 8167, 8171, 8179, 8191, 8209, 8219, 8221, 8231, 8233, 8237, 8243, 8263, 8269, 8273, 8287, 8291, 8293, 8297, 8311, 8317, 8329, 8353, 8363, 8369, 8377, 8387, 8389, 8419, 8423, 8429, 8431, 8443, 8447, 8461, 8467, 8501, 8513, 8521, 8527, 8537, 8539, 8543, 8563, 8573, 8581, 8597, 8599, 8609, 8623, 8627, 8629, 8641, 8647, 8663, 8669, 8677, 8681, 8689, 8693, 8699, 8707, 8713, 8719, 8731, 8737, 8741, 8747, 8753, 8761, 8779, 8783, 8803, 8807, 8819, 8821, 8831, 8837, 8839, 8849, 8861, 8863, 8867, 8887, 8893, 8923, 8929, 8933, 8941, 8951, 8963, 8969, 8971, 8999, 9001, 9007, 9011, 9013, 9029, 9041, 9043, 9049, 9059, 9067, 9091, 9103, 9109, 9127, 9133, 9137, 9151, 9157, 9161, 9173, 9181, 9187, 9199, 9203, 9209, 9221, 9227, 9239, 9241, 9257, 9277, 9281, 9283, 9293, 9311, 9319, 9323, 9337, 9341, 9343, 9349, 9371, 9377, 9391, 9397, 9403, 9413, 9419, 9421, 9431, 9433, 9437, 9439, 9461, 9463, 9467, 9473, 9479, 9491, 9497, 9511, 9521, 9533, 9539, 9547, 9551, 9587, 9601, 9613, 9619, 9623, 9629, 9631, 9643, 9649, 9661, 9677, 9679, 9689, 9697, 9719, 9721, 9733, 9739, 9743, 9749, 9767, 9769, 9781, 9787, 9791, 9803, 9811, 9817, 9829, 9833, 9839, 9851, 9857, 9859, 9871, 9883, 9887, 9901, 9907, 9923, 9929, 9931, 9941, 9949, 9967, 9973]

end RosserSieveData


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

end RosserPackedBarrier

namespace RosserBitMoments
open RosserBitSieve
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

end RosserBitMoments


namespace RosserScan
open RosserBitSieve
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

end RosserScan


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

namespace RosserSieveData

theorem divisors_ge_two : ∀ d ∈ divisors, 2 ≤ d := by decide +kernel

end RosserSieveData


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

end RosserPackedMoments

namespace RosserFastCompute

def depthFor (len : ℕ) : ℕ :=
  if len ≤ 8 then 0 else Nat.log2 ((len - 1) / 8) + 1

end RosserFastCompute


namespace RosserMediumSqrtChain
open RosserScan
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

end RosserMediumSqrtChain


end OddGoldbachWideAccepted


set_option autoImplicit false

open Finset Real
namespace OddGoldbachPsi

/-- A finite prime-count bound controls the additional prime-power terms. -/
theorem psi_le_theta_add_count_log_sub (n r b : ℕ)
    (hn : n ≠ 0) (hrn : r ≤ n) (hnb : n ≤ b)
    (hb : b < (r + 1) ^ 2) :
    Chebyshev.psi n ≤ Chebyshev.theta n +
      (Nat.primesLE r).card * Real.log b - Chebyshev.theta r := by
  have hs : (Nat.primesLE n).filter (fun p => p ≤ r) = Nat.primesLE r := by
    ext p
    simp only [mem_filter, Nat.mem_primesLE]
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h.1.trans hrn, h.2⟩, h.1⟩⟩
  have hsum : ∀ p ∈ Nat.primesLE n,
      (Nat.log p n : ℝ) * Real.log p ≤
        Real.log p + if p ≤ r then Real.log b - Real.log p else 0 := by
    intro p hp
    have hpprime := (Nat.mem_primesLE.mp hp).2
    by_cases hpr : p ≤ r
    · simp only [hpr, if_true]
      have hlog : (Nat.log p n : ℝ) * Real.log p ≤ Real.log b := by
        apply Real.le_log_of_pow_le (by exact_mod_cast hpprime.pos)
        exact_mod_cast (Nat.pow_log_le_self p hn).trans hnb
      linarith
    · simp only [hpr, if_false, add_zero]
      have hp2 : n < p ^ 2 := by
        have hple : r + 1 ≤ p := by omega
        have hpow := Nat.pow_le_pow_left hple 2
        omega
      have hlog : Nat.log p n ≤ 1 := by
        have := Nat.log_lt_of_lt_pow hn hp2
        omega
      calc
        (Nat.log p n : ℝ) * Real.log p ≤ 1 * Real.log p :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hlog)
            (Real.log_natCast_nonneg p)
        _ = _ := one_mul _
  calc
    Chebyshev.psi n = ∑ p ∈ Nat.primesLE n,
        (Nat.log p n : ℝ) * Real.log p := Chebyshev.psi_eq_sum_mul_log_prime n
    _ ≤ ∑ p ∈ Nat.primesLE n,
        (Real.log p + if p ≤ r then Real.log b - Real.log p else 0) :=
      sum_le_sum hsum
    _ = Chebyshev.theta n +
        (Nat.primesLE r).card * Real.log b - Chebyshev.theta r := by
      rw [sum_add_distrib, ← sum_filter, hs, sum_sub_distrib, sum_const]
      simp only [nsmul_eq_mul, Chebyshev.theta_eq_sum_primesLE_log]
      ring

end OddGoldbachPsi

namespace OddGoldbachPsi

lemma theta_ge_twenty (r : ℕ) (hr : 31 ≤ r) : 20 ≤ Chebyshev.theta r := by
  have hprod : primorial 31 = 200560490130 := by decide +kernel
  have hlarge : (2 : ℝ) ^ 30 ≤ primorial 31 := by rw [hprod]; norm_num
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ 30) hlarge
  rw [Real.log_pow] at hlog
  have htwo := Real.log_two_gt_d9
  have htheta : 20 ≤ Chebyshev.theta (31 : ℝ) := by
    rw [Chebyshev.theta_eq_log_primorial]
    norm_num only [Nat.floor_natCast] at *
    linarith
  exact htheta.trans (Chebyshev.theta_mono (by exact_mod_cast hr))

lemma theta_step (a b c : ℕ) (hab : a ≤ b)
    (hc : (Nat.primesLE b \ Nat.primesLE a).card ≤ c) :
    Chebyshev.theta b ≤ Chebyshev.theta a + c * Real.log b := by
  have hsub := Nat.primesLE_mono hab
  have hsum : ∑ p ∈ Nat.primesLE b \ Nat.primesLE a, Real.log p ≤ c * Real.log b := by
    calc
      _ ≤ ∑ _p ∈ Nat.primesLE b \ Nat.primesLE a, Real.log b := by
        apply sum_le_sum
        intro p hp
        obtain ⟨hp, _⟩ := mem_sdiff.mp hp
        apply Real.log_le_log (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.pos)
        exact_mod_cast (Nat.mem_primesLE.mp hp).1
      _ = (Nat.primesLE b \ Nat.primesLE a).card * Real.log b := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (Real.log_natCast_nonneg b)
  have heq := Finset.sum_sdiff hsub (f := fun p : ℕ => Real.log p)
  rw [← Chebyshev.theta_eq_sum_primesLE_log, ← Chebyshev.theta_eq_sum_primesLE_log] at heq
  linarith

end OddGoldbachPsi

namespace OddGoldbachPsi

def logUpperRat (n k : ℕ) : ℚ :=
  let z : ℚ := ((n : ℚ) - 2 ^ k) / ((n : ℚ) + 2 ^ k)
  (k : ℚ) * (6931471808 / 10000000000) +
    2 * ((∑ i ∈ Finset.range 8, z ^ (2 * i + 1) / (2 * i + 1 : ℕ)) +
      z ^ 17 / (1 - z ^ 2))

lemma logUpperRat_sound (n k : ℕ) (hk : 2 ^ k ≤ n) :
    Real.log n ≤ (logUpperRat n k : ℝ) := by
  let z : ℝ := ((n : ℝ) - 2 ^ k) / ((n : ℝ) + 2 ^ k)
  have hkn : (2 : ℝ) ^ k ≤ n := by exact_mod_cast hk
  have htwo : (0 : ℝ) < 2 ^ k := by positivity
  have hn : (0 : ℝ) < n := htwo.trans_le hkn
  have hden : (0 : ℝ) < n + 2 ^ k := by positivity
  have hz : 0 ≤ z := div_nonneg (sub_nonneg.mpr hkn) hden.le
  have hz1 : z < 1 := by
    dsimp [z]
    rw [div_lt_one hden]
    linarith
  have h := Real.log_div_le_sum_range_add hz hz1 8
  have hratio : (1 + z) / (1 - z) = n / (2 : ℝ) ^ k := by
    dsimp [z]
    field_simp
    ring
  rw [hratio, Real.log_div hn.ne' htwo.ne', Real.log_pow] at h
  have hcast : (logUpperRat n k : ℝ) =
      (k : ℝ) * (6931471808 / 10000000000) +
        2 * ((∑ i ∈ Finset.range 8, z ^ (2 * i + 1) / (2 * i + 1 : ℕ)) +
          z ^ 17 / (1 - z ^ 2)) := by
    simp only [logUpperRat, z]
    push_cast
    rfl
  rw [hcast]
  have htwoBound := mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  norm_num only [Nat.reduceMul, Nat.reduceAdd, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at h ⊢
  linarith

end OddGoldbachPsi


set_option autoImplicit false
set_option Elab.async false

namespace OddGoldbachPsi
open OddGoldbachWideAccepted RosserBitSieve RosserBitMoments RosserPackedMoments RosserScan

def countBytes (mask stripe : ℕ) : ℕ → ℕ → ℕ
  | 0, total => total
  | j + 1, total =>
    forceNat ((mask >>> j) &&& stripe) fun bit =>
      forceNat (total + bit) (countBytes mask stripe j)

def countCombine (bits half count : ℕ) : ℕ :=
  let stripe := periodicMask (2 * half) (bits / (2 * half)) * (2 ^ half - 1)
  forceNat stripe fun stripe => (count &&& stripe) + ((count >>> half) &&& stripe)

def countReduce (bits : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, total => total
  | fuel + 1, half, total =>
    forceNat (countCombine bits half total) (countReduce bits fuel (2 * half))

def fastCount (depth mask : ℕ) : ℕ :=
  let bits := 2 ^ (depth + 3)
  forceNat (periodicMask 8 (bits / 8)) fun stripe =>
    forceNat (countBytes mask stripe 8 0) (countReduce bits depth 8)

lemma countBytes_eq (mask stripe j : ℕ) (state : Moments) :
    countBytes mask stripe j state.count = (bytes mask stripe j state).count := by
  induction j generalizing state with
  | zero => rfl
  | succ j ih =>
    simp only [countBytes, bytes, forceNat_eq, strictMoments_eq]
    exact ih ⟨state.count + ((mask >>> j) &&& stripe),
      state.first + j * ((mask >>> j) &&& stripe),
      state.second + j * j * ((mask >>> j) &&& stripe)⟩

lemma countCombine_eq (bits half : ℕ) (state : Moments) :
    countCombine bits half state.count = (combine bits half state).count := by
  simp only [countCombine, combine, forceNat_eq]

lemma countReduce_eq (bits fuel half : ℕ) (state : Moments) :
    countReduce bits fuel half state.count = (reduce bits fuel half state).count := by
  induction fuel generalizing half state with
  | zero => rfl
  | succ fuel ih =>
    simp only [countReduce, reduce, forceNat_eq, strictMoments_eq, countCombine_eq]
    exact ih _ _

lemma fastCount_eq (depth mask : ℕ) : fastCount depth mask = (packedMoments depth mask).count := by
  simp only [fastCount, packedMoments, forceNat_eq, strictMoments_eq, translate]
  rw [show countBytes mask (periodicMask 8 (2 ^ (depth + 3) / 8)) 8 0 =
    (bytes mask (periodicMask 8 (2 ^ (depth + 3) / 8)) 8 ⟨0, 0, 0⟩).count from
      countBytes_eq _ _ _ ⟨0, 0, 0⟩]
  exact countReduce_eq _ _ _ _

end OddGoldbachPsi


set_option autoImplicit false
set_option Elab.async false

namespace OddGoldbachPsi
open Finset Real OddGoldbachWideAccepted
open RosserBitSieve RosserBitMoments RosserPackedMoments RosserScan

def scale : ℕ := 1000000

def bitCount (depth mask : ℕ) : ℕ :=
  forceNat mask fun value => fastCount depth value

lemma bitCount_sound (depth mask len : ℕ) (hm : mask < 2 ^ len)
    (hlen : len ≤ 2 ^ (depth + 3)) :
    bitCount depth mask = RosserPackedBarrier.candidateCount mask len := by
  rw [bitCount, forceNat_eq, fastCount_eq, packedMoments_sound depth mask
    (hm.trans_le (Nat.pow_le_pow_right (by norm_num) hlen))]
  exact (candidateCount_eq_enumBits_length depth mask len hm hlen).symm

lemma depthFor_covers (len : ℕ) : len ≤ 2 ^ (RosserFastCompute.depthFor len + 3) := by
  unfold RosserFastCompute.depthFor
  split_ifs with h
  · norm_num
    exact h
  · rw [pow_add]
    norm_num only [Nat.reducePow]
    have ht := Nat.lt_log2_self (n := (len - 1) / 8)
    omega

def smallMask (r : ℕ) : ℕ := candidateMask [2, 3, 5, 7] 8 (r - 7)
def smallCount (r : ℕ) : ℕ := 4 + bitCount (RosserFastCompute.depthFor (r - 7)) (smallMask r)

lemma smallCount_sound (r : ℕ) (hr : 7 ≤ r) (_hr' : r ≤ 10000) :
    (Nat.primesLE r).card ≤ smallCount r := by
  have hcover := sieve_covers [2, 3, 5, 7] 7 r (by decide :
    ∀ d ∈ [2, 3, 5, 7], 2 ≤ d ∧ d < 7 + 1)
  have hc := RosserPrefixBridge.prime_card_le_candidateCount 7 r r (smallMask r)
    hr le_rfl hcover
  have hm : smallMask r < 2 ^ (r - 7) := by
    unfold smallMask candidateMask
    apply Nat.xor_lt_two_pow
    · exact Nat.sub_lt (by positivity) (by norm_num)
    · exact Nat.mod_lt _ (by positivity)
  rw [← bitCount_sound _ (smallMask r) (r - 7) hm (depthFor_covers _)] at hc
  have hcard := Finset.card_sdiff_add_card_eq_card (Nat.primesLE_mono hr)
  have hsmall : (Nat.primesLE 7).card = 4 := by decide +kernel
  rw [hsmall] at hcard
  unfold smallCount
  omega

structure Block where
  a : ℕ
  b : ℕ
  initial : ℕ
  final : ℕ
  logNumerator : ℕ

def window (mask base : ℕ) (c : Block) : ℕ :=
  mask / 2 ^ (c.a - base) % 2 ^ (c.b - c.a)

def Valid (base top mask : ℕ) (c : Block) : Prop :=
  base ≤ c.a ∧ c.b ≤ top ∧ c.a < c.b ∧
  c.b - c.a ≤ 2 ^ (RosserFastCompute.depthFor (c.b - c.a) + 3) ∧
  2 ^ Nat.log2 c.b ≤ c.b ∧
  logUpperRat c.b (Nat.log2 c.b) ≤ (c.logNumerator : ℚ) / scale ∧
  c.initial + bitCount (RosserFastCompute.depthFor (c.b - c.a)) (window mask base c) *
    c.logNumerator ≤ c.final ∧
  (c.b ≤ 1000 ∨
    (1000 ≤ c.a ∧ 31 ≤ Nat.sqrt c.b ∧ Nat.sqrt c.b ≤ c.a + 1 ∧
      Nat.sqrt c.b ≤ 10000 ∧ c.b < (Nat.sqrt c.b + 1) ^ 2 ∧
      100000 * (c.final + smallCount (Nat.sqrt c.b) * c.logNumerator) <
        103883 * (c.a + 1) * scale + 2000000 * scale))

instance (base top mask : ℕ) (c : Block) : Decidable (Valid base top mask c) := by
  unfold Valid
  infer_instance

def Good (c : Block) : Prop :=
  Chebyshev.theta c.a ≤ (c.initial : ℝ) / scale →
    Chebyshev.theta c.b ≤ (c.final : ℝ) / scale ∧
      ∀ n : ℕ, 1000 < n → c.a < n → n ≤ c.b →
        Chebyshev.psi n < 1.03883 * (n : ℝ)

lemma block_sound (base top mask : ℕ) (c : Block)
    (hcover : Covers base top mask) (h : Valid base top mask c) : Good c := by
  obtain ⟨hba, hbt, hab, hlen, hk, hlog, hstep, hbound⟩ := h
  have hm : window mask base c < 2 ^ (c.b - c.a) := Nat.mod_lt _ (by positivity)
  have hcard := RosserPrefixBridge.prime_card_le_candidateCount c.a c.b c.b
    (window mask base c) hab.le le_rfl
    (RosserPrefixBridge.window_mask_covers base top mask c.a c.b hcover hba hbt)
  rw [← bitCount_sound _ _ _ hm hlen] at hcard
  have hl : Real.log c.b ≤ (c.logNumerator : ℝ) / scale := by
    apply (logUpperRat_sound c.b (Nat.log2 c.b) hk).trans
    have hh : (logUpperRat c.b (Nat.log2 c.b) : ℝ) ≤
        (((c.logNumerator : ℚ) / scale : ℚ) : ℝ) := Rat.cast_le.mpr hlog
    simpa only [Rat.cast_div, Rat.cast_natCast] using hh
  intro hv
  have ht : Chebyshev.theta c.b ≤ (c.final : ℝ) / scale := by
    have hs := theta_step c.a c.b _ hab.le hcard
    have hnonneg : (0 : ℝ) ≤ bitCount (RosserFastCompute.depthFor (c.b - c.a))
        (window mask base c) := Nat.cast_nonneg _
    have hmul := mul_le_mul_of_nonneg_left hl hnonneg
    have hh : (c.initial : ℝ) + bitCount (RosserFastCompute.depthFor (c.b - c.a))
        (window mask base c) * c.logNumerator ≤ c.final := by exact_mod_cast hstep
    simp only [scale, Nat.cast_ofNat] at hv hs hmul hh ⊢
    nlinarith
  refine ⟨ht, ?_⟩
  intro n hn han hnb
  rcases hbound with hlo | hbound
  · omega
  obtain ⟨ha, hr, hrn, hrmax, hrpow, hineq⟩ := hbound
  have hsn : Nat.sqrt c.b ≤ n := by omega
  have hp := psi_le_theta_add_count_log_sub n (Nat.sqrt c.b) c.b
    (by omega) hsn hnb hrpow
  have htheta := theta_ge_twenty (Nat.sqrt c.b) hr
  have hc := smallCount_sound (Nat.sqrt c.b) (by omega) hrmax
  have hc' : ((Nat.primesLE (Nat.sqrt c.b)).card : ℝ) ≤ smallCount (Nat.sqrt c.b) := by
    exact_mod_cast hc
  have hcount := mul_le_mul_of_nonneg_right hc' (Real.log_natCast_nonneg c.b)
  have hlog' := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg (smallCount (Nat.sqrt c.b)) :
    (0 : ℝ) ≤ smallCount (Nat.sqrt c.b))
  have hmono := Chebyshev.theta_mono (by exact_mod_cast hnb : (n : ℝ) ≤ c.b)
  have hi : (100000 : ℝ) * (c.final + smallCount (Nat.sqrt c.b) * c.logNumerator) <
      103883 * ((c.a : ℝ) + 1) * scale + 2000000 * scale := by exact_mod_cast hineq
  have hn' : (c.a : ℝ) + 1 ≤ n := by exact_mod_cast han
  simp only [scale, Nat.cast_ofNat] at ht hlog' hi
  generalize hq : smallCount (Nat.sqrt c.b) = q at *
  nlinarith only [hp, htheta, hcount, hlog', hmono, ht, hi, hn']

end OddGoldbachPsi

namespace OddGoldbachPsi
open OddGoldbachWideAccepted RosserScan

structure Group where
  base : ℕ
  top : ℕ
  blocks : List Block

def checkBlock (base top mask : ℕ) (c : Block) : Bool :=
  decide (Valid base top mask c)

def checkGroup (ds : List (ℕ × ℕ)) (g : Group) : Bool :=
  decide (g.base < g.top ∧ g.top - g.base ≤ 1048576) &&
    forceNat (RosserMediumSqrtChain.mask ds g.base g.top) fun mask =>
      g.blocks.all (checkBlock g.base g.top mask)

def checkGroups (groups : List Group) : Bool :=
  RosserCachedSieve.withMasks 1048576 RosserSieveData.divisors fun ds =>
    groups.all (checkGroup ds)

lemma checkGroups_append (xs ys : List Group) :
    checkGroups (xs ++ ys) = (checkGroups xs && checkGroups ys) := by
  simp only [checkGroups, RosserCachedSieve.withMasks_eq, List.all_append]

lemma checkGroups_sound (groups : List Group) (h : checkGroups groups = true) :
    ∀ c ∈ groups.flatMap Group.blocks, Good c := by
  unfold checkGroups at h
  rw [RosserCachedSieve.withMasks_eq] at h
  intro c hc
  obtain ⟨g, hg, hc⟩ := List.mem_flatMap.mp hc
  have hg' := List.all_eq_true.mp h g hg
  simp only [checkGroup, Bool.and_eq_true, decide_eq_true_eq, forceNat_eq] at hg'
  have hcover := RosserMediumSqrtChain.mask_prime 1048576 g.base g.top
    RosserSieveData.divisors RosserSieveData.divisors_ge_two hg'.1.1 hg'.1.2
  have hgood := List.all_eq_true.mp hg'.2 c hc
  exact block_sound _ _ _ c hcover (of_decide_eq_true hgood)

def linked (a initial top final : ℕ) : List Block → Bool
  | [] => decide (a = top ∧ initial = final)
  | c :: cs => decide (c.a = a ∧ c.initial = initial) &&
      linked c.b c.final top final cs

lemma linked_sound (blocks : List Block) (a initial top final : ℕ)
    (hg : ∀ c ∈ blocks, Good c)
    (hl : linked a initial top final blocks = true)
    (ht : Chebyshev.theta a ≤ (initial : ℝ) / scale) :
    Chebyshev.theta top ≤ (final : ℝ) / scale ∧
      ∀ n : ℕ, 1000 < n → a < n → n ≤ top →
        Chebyshev.psi n < 1.03883 * (n : ℝ) := by
  induction blocks generalizing a initial with
  | nil =>
    simp only [linked, decide_eq_true_eq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    exact ⟨ht, by omega⟩
  | cons c cs ih =>
    simp only [linked, Bool.and_eq_true, decide_eq_true_eq] at hl
    obtain ⟨⟨rfl, rfl⟩, hl⟩ := hl
    obtain ⟨hnext, hblock⟩ := hg c (by simp) ht
    have hrest := ih c.b c.final (fun d hd => hg d (by simp [hd])) hl hnext
    refine ⟨hrest.1, ?_⟩
    intro n hn han hnt
    by_cases hnb : n ≤ c.b
    · exact hblock n hn han hnb
    · exact hrest.2 n hn (by omega) hnt

lemma certificate_sound (groups : List Group) (final : ℕ)
    (hg : checkGroups groups = true)
    (hl : linked 1 0 100000000 final (groups.flatMap Group.blocks) = true) :
    ∀ n : ℕ, 1000 < n → n < 10 ^ 8 →
      Chebyshev.psi n < 1.03883 * (n : ℝ) := by
  have hstart : Chebyshev.theta (1 : ℝ) ≤ (0 : ℝ) / scale := by
    rw [Chebyshev.theta_eq_zero_of_lt_two (by norm_num)]
    simp
  have h := linked_sound (groups.flatMap Group.blocks) 1 0 100000000 final
    (checkGroups_sound groups hg) hl (by simpa using hstart)
  intro n hn hN
  exact h.2 n hn (by omega) (by norm_num at hN; omega)

end OddGoldbachPsi

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace OddGoldbachPsi

def rangeGroups00 : List Group := [
  ⟨55574528, 56623104, [
    ⟨55574528, 55852400, 55572198560551, 55851777060976, 17838225⟩,
    ⟨55852400, 56131662, 55851777060976, 56131612154772, 17843212⟩,
    ⟨56131662, 56412320, 56131612154772, 56411793198372, 17848200⟩,
    ⟨56412320, 56623104, 56411793198372, 56622124625850, 17851929⟩
  ]⟩,
  ⟨56623104, 57671680, [
    ⟨56623104, 56906219, 56622124625850, 56907031736585, 17856917⟩,
    ⟨56906219, 57190750, 56907031736585, 57191500419689, 17861904⟩,
    ⟨57190750, 57476703, 57191500419689, 57477745896421, 17866892⟩,
    ⟨57476703, 57671680, 57477745896421, 57673139516073, 17870278⟩
  ]⟩,
  ⟨57671680, 58720256, [
    ⟨57671680, 57960038, 57673139516073, 57960287789097, 17875266⟩,
    ⟨57960038, 58249838, 57960287789097, 58249715444408, 17880253⟩,
    ⟨58249838, 58541087, 58249715444408, 58540744085960, 17885241⟩,
    ⟨58541087, 58720256, 58540744085960, 58720557247404, 17888297⟩
  ]⟩,
  ⟨58720256, 59768832, [
    ⟨58720256, 59013857, 58720557247404, 59014579690092, 17893284⟩,
    ⟨59013857, 59308926, 59014579690092, 59308630400780, 17898272⟩,
    ⟨59308926, 59605470, 59308630400780, 59604893530712, 17903259⟩,
    ⟨59605470, 59768832, 59604893530712, 59768267838216, 17905996⟩
  ]⟩,
  ⟨59768832, 60817408, [
    ⟨59768832, 60067676, 59768267838216, 60067345449048, 17910984⟩,
    ⟨60067676, 60368014, 60067345449048, 60368065022283, 17915971⟩,
    ⟨60368014, 60669854, 60368065022283, 60670409521572, 17920959⟩,
    ⟨60669854, 60817408, 60670409521572, 60818277472572, 17923388⟩
  ]⟩,
  ⟨60817408, 61865984, [
    ⟨60817408, 61121495, 60818277472572, 61122916437564, 17928376⟩,
    ⟨61121495, 61427102, 61122916437564, 61426097872442, 17933363⟩,
    ⟨61427102, 61734237, 61426097872442, 61732843674542, 17938351⟩,
    ⟨61734237, 61865984, 61732843674542, 61864598581694, 17940483⟩
  ]⟩,
  ⟨61865984, 62914560, [
    ⟨61865984, 62175313, 61864598581694, 62174714248764, 17945470⟩,
    ⟨62175313, 62486189, 62174714248764, 62485221271248, 17950458⟩,
    ⟨62486189, 62798619, 62485221271248, 62797987167703, 17955445⟩,
    ⟨62798619, 62914560, 62797987167703, 62913757816333, 17957290⟩
  ]⟩,
  ⟨62914560, 63963136, [
    ⟨62914560, 63229132, 62913757816333, 63227882116509, 17962277⟩,
    ⟨63229132, 63545277, 63227882116509, 63544662965724, 17967265⟩,
    ⟨63545277, 63863003, 63544662965724, 63863275049180, 17972252⟩,
    ⟨63863003, 63963136, 63863275049180, 63964198042865, 17973819⟩
  ]⟩
]

theorem rangeChecked00 : checkGroups rangeGroups00 = true := by decide +kernel

def rangeGroups01 : List Group := [
  ⟨63963136, 65011712, [
    ⟨63963136, 64282951, 63964198042865, 64283879210132, 17978807⟩,
    ⟨64282951, 64604365, 64283879210132, 64604116629890, 17983794⟩,
    ⟨64604365, 64927386, 64604116629890, 64925774040832, 17988782⟩,
    ⟨64927386, 65011712, 64925774040832, 65010075551026, 17990079⟩
  ]⟩,
  ⟨65011712, 66060288, [
    ⟨65011712, 65336770, 65010075551026, 65334832525175, 17995067⟩,
    ⟨65336770, 65663453, 65334832525175, 65661047521940, 18000055⟩,
    ⟨65663453, 65991770, 65661047521940, 65990719840960, 18005042⟩,
    ⟨65991770, 66060288, 65990719840960, 66059755151680, 18006080⟩
  ]⟩,
  ⟨66060288, 67108864, [
    ⟨66060288, 66390589, 66059755151680, 66392383537036, 18011067⟩,
    ⟨66390589, 66722541, 66392383537036, 66724347366466, 18016055⟩,
    ⟨66722541, 67056153, 66724347366466, 67057214033248, 18021042⟩,
    ⟨67056153, 67108864, 67057214033248, 67110108098428, 18021828⟩
  ]⟩,
  ⟨67108864, 68157440, [
    ⟨67108864, 67444408, 67110108098428, 67446596645884, 18026816⟩,
    ⟨67444408, 67781630, 67446596645884, 67784043807226, 18031803⟩,
    ⟨67781630, 68120538, 67784043807226, 68123424066682, 18036791⟩,
    ⟨68120538, 68157440, 68123424066682, 68160184149298, 18037332⟩
  ]⟩,
  ⟨68157440, 69206016, [
    ⟨68157440, 68498227, 68160184149298, 68501147912658, 18042320⟩,
    ⟨68498227, 68840718, 68501147912658, 68842079589195, 18047307⟩,
    ⟨68840718, 69184921, 68842079589195, 69186011913535, 18052295⟩,
    ⟨69184921, 69206016, 69186011913535, 69206934876935, 18052600⟩
  ]⟩,
  ⟨69206016, 70254592, [
    ⟨69206016, 69552046, 69206934876935, 69554290620467, 18057587⟩,
    ⟨69552046, 69899806, 69554290620467, 69902482878742, 18062575⟩,
    ⟨69899806, 70249305, 69902482878742, 70251566244144, 18067562⟩,
    ⟨70249305, 70254592, 70251566244144, 70256643250422, 18067638⟩
  ]⟩,
  ⟨70254592, 71303168, [
    ⟨70254592, 70605864, 70256643250422, 70609926923922, 18072625⟩,
    ⟨70605864, 70958893, 70609926923922, 70960451839992, 18077613⟩,
    ⟨70958893, 71303168, 70960451839992, 71305012981907, 18082453⟩
  ]⟩,
  ⟨71303168, 72351744, [
    ⟨71303168, 71659683, 71305012981907, 71663397518067, 18087440⟩,
    ⟨71659683, 72017981, 71663397518067, 72019709795099, 18092428⟩,
    ⟨72017981, 72351744, 72019709795099, 72356495932819, 18097052⟩
  ]⟩
]

theorem rangeChecked01 : checkGroups rangeGroups01 = true := by decide +kernel

def rangeGroups02 : List Group := [
  ⟨72351744, 73400320, [
    ⟨72351744, 72713502, 72356495932819, 72717631610869, 18102039⟩,
    ⟨72713502, 73077069, 72717631610869, 73081981208163, 18107027⟩,
    ⟨73077069, 73400320, 73081981208163, 73404328617283, 18111440⟩
  ]⟩,
  ⟨73400320, 74448896, [
    ⟨73400320, 73767321, 73404328617283, 73771367448563, 18116428⟩,
    ⟨73767321, 74136157, 73771367448563, 74139014716083, 18121415⟩,
    ⟨74136157, 74448896, 74139014716083, 74451808626708, 18125625⟩
  ]⟩,
  ⟨74448896, 75497472, [
    ⟨74448896, 74821140, 74451808626708, 74823613107499, 18130613⟩,
    ⟨74821140, 75195245, 74823613107499, 75197750535499, 18135600⟩,
    ⟨75195245, 75497472, 75197750535499, 75501353204806, 18139611⟩
  ]⟩,
  ⟨75497472, 76546048, [
    ⟨75497472, 75874959, 75501353204806, 75880049130535, 18144599⟩,
    ⟨75874959, 76254333, 75880049130535, 76258921738285, 18149586⟩,
    ⟨76254333, 76546048, 76258921738285, 76549666672765, 18153405⟩
  ]⟩,
  ⟨76546048, 77594624, [
    ⟨76546048, 76928778, 76549666672765, 76930702370493, 18158392⟩,
    ⟨76928778, 77313421, 76930702370493, 77316256437753, 18163380⟩,
    ⟨77313421, 77594624, 77316256437753, 77597572587603, 18167010⟩
  ]⟩,
  ⟨77594624, 78643200, [
    ⟨77594624, 77982597, 77597572587603, 77985199476941, 18171998⟩,
    ⟨77982597, 78372509, 77985199476941, 78373859770211, 18176985⟩,
    ⟨78372509, 78643200, 78373859770211, 78643730117663, 18180433⟩
  ]⟩,
  ⟨78643200, 79691776, [
    ⟨78643200, 79036416, 78643730117663, 79036971661367, 18185421⟩,
    ⟨79036416, 79431598, 79036971661367, 79432722177815, 18190408⟩,
    ⟨79431598, 79691776, 79432722177815, 79692436931265, 18193678⟩
  ]⟩,
  ⟨79691776, 80740352, [
    ⟨79691776, 80090234, 79692436931265, 80089895796705, 18198666⟩,
    ⟨80090234, 80490685, 80089895796705, 80491523014907, 18203654⟩,
    ⟨80490685, 80740352, 80491523014907, 80740409301077, 18206751⟩
  ]⟩
]

theorem rangeChecked02 : checkGroups rangeGroups02 = true := by decide +kernel

def rangeGroups03 : List Group := [
  ⟨80740352, 81788928, [
    ⟨80740352, 81144053, 80740409301077, 81148024420993, 18211738⟩,
    ⟨81144053, 81549773, 81148024420993, 81553455874849, 18216726⟩,
    ⟨81549773, 81788928, 81553455874849, 81792224440519, 18219654⟩
  ]⟩,
  ⟨81788928, 82837504, [
    ⟨81788928, 82197872, 81792224440519, 82201622775943, 18224641⟩,
    ⟨82197872, 82608861, 82201622775943, 82611825887701, 18229629⟩,
    ⟨82608861, 82837504, 82611825887701, 82841699898645, 18232393⟩
  ]⟩,
  ⟨82837504, 83886080, [
    ⟨82837504, 83251691, 82841699898645, 83254247671625, 18237380⟩,
    ⟨83251691, 83667949, 83254247671625, 83669644633353, 18242368⟩,
    ⟨83667949, 83886080, 83669644633353, 83889241116345, 18244972⟩
  ]⟩,
  ⟨83886080, 84934656, [
    ⟨83886080, 84305510, 83889241116345, 84307785676051, 18249959⟩,
    ⟨84305510, 84727037, 84307785676051, 84728781263765, 18254947⟩,
    ⟨84727037, 84934656, 84728781263765, 84935327162087, 18257394⟩
  ]⟩,
  ⟨84934656, 85983232, [
    ⟨84934656, 85359329, 84935327162087, 85359726657385, 18262382⟩,
    ⟨85359329, 85786125, 85359726657385, 85787091755140, 18267369⟩,
    ⟨85786125, 85983232, 85787091755140, 85984678171300, 18269664⟩
  ]⟩,
  ⟨85983232, 87031808, [
    ⟨85983232, 86413148, 85984678171300, 86413913197476, 18274652⟩,
    ⟨86413148, 86845213, 86413913197476, 86846592252606, 18279639⟩,
    ⟨86845213, 87031808, 86846592252606, 87033761177674, 18281786⟩
  ]⟩,
  ⟨87031808, 88080384, [
    ⟨87031808, 87466967, 87033761177674, 87467157697774, 18286773⟩,
    ⟨87466967, 87904301, 87467157697774, 87904641745611, 18291761⟩,
    ⟨87904301, 88080384, 87904641745611, 88082109530773, 18293762⟩
  ]⟩,
  ⟨88080384, 89128960, [
    ⟨88080384, 88520785, 88082109530773, 88522340834215, 18298749⟩,
    ⟨88520785, 88963388, 88522340834215, 88965657344355, 18303737⟩,
    ⟨88963388, 89128960, 88965657344355, 89130938570639, 18305596⟩
  ]⟩
]

theorem rangeChecked03 : checkGroups rangeGroups03 = true := by decide +kernel

def rangeGroups04 : List Group := [
  ⟨89128960, 90177536, [
    ⟨89128960, 89574604, 89130938570639, 89575537860743, 18310584⟩,
    ⟨89574604, 90022477, 89575537860743, 90021375490025, 18315571⟩,
    ⟨90022477, 90177536, 90021375490025, 90177585356201, 18317292⟩
  ]⟩,
  ⟨90177536, 91226112, [
    ⟨90177536, 90628423, 90177585356201, 90629394458721, 18322280⟩,
    ⟨90628423, 91081565, 90629394458721, 91082261226291, 18327267⟩,
    ⟨91081565, 91226112, 91082261226291, 91227627359434, 18328853⟩
  ]⟩,
  ⟨91226112, 92274688, [
    ⟨91226112, 91682242, 91227627359434, 91684250003380, 18333841⟩,
    ⟨91682242, 92140653, 91684250003380, 92142463959788, 18338828⟩,
    ⟨92140653, 92274688, 92142463959788, 92275761129364, 18340282⟩
  ]⟩,
  ⟨92274688, 93323264, [
    ⟨92274688, 92736061, 92275761129364, 92737438169018, 18345269⟩,
    ⟨92736061, 93199741, 92737438169018, 93199791244390, 18350257⟩,
    ⟨93199741, 93323264, 93199791244390, 93322489914956, 18351581⟩
  ]⟩,
  ⟨93323264, 94371840, [
    ⟨93323264, 93789880, 93322489914956, 93788599915004, 18356569⟩,
    ⟨93789880, 94258829, 93788599915004, 94259426959598, 18361557⟩,
    ⟨94258829, 94371840, 94259426959598, 94371458127853, 18362755⟩
  ]⟩,
  ⟨94371840, 95420416, [
    ⟨94371840, 94843699, 94371458127853, 94844886677903, 18367742⟩,
    ⟨94843699, 95317917, 94844886677903, 95320464793953, 18372730⟩,
    ⟨95317917, 95420416, 95320464793953, 95422696644973, 18373805⟩
  ]⟩,
  ⟨95420416, 96468992, [
    ⟨95420416, 95897518, 95422696644973, 95900140903549, 18378792⟩,
    ⟨95897518, 96377005, 95900140903549, 96378523626709, 18383780⟩,
    ⟨96377005, 96468992, 96378523626709, 96470906915059, 18384734⟩
  ]⟩,
  ⟨96468992, 97517568, [
    ⟨96468992, 96951336, 96470906915059, 96953269296889, 18389721⟩,
    ⟨96951336, 97436092, 96953269296889, 97437657168986, 18394709⟩,
    ⟨97436092, 97517568, 97437657168986, 97520694659116, 18395545⟩
  ]⟩
]

theorem rangeChecked04 : checkGroups rangeGroups04 = true := by decide +kernel

def rangeGroups05 : List Group := [
  ⟨97517568, 98566144, [
    ⟨97517568, 98005155, 97520694659116, 98009467990632, 18400532⟩,
    ⟨98005155, 98495180, 98009467990632, 98498134546632, 18405520⟩,
    ⟨98495180, 98566144, 98498134546632, 98570544694792, 18406240⟩
  ]⟩,
  ⟨98566144, 99614720, [
    ⟨98566144, 99058974, 98570544694792, 99061111838207, 18411227⟩,
    ⟨99058974, 99554268, 99061111838207, 99554408573197, 18416215⟩,
    ⟨99554268, 99614720, 99554408573197, 99616418012871, 18416822⟩
  ]⟩,
  ⟨99614720, 100000000, [
    ⟨99614720, 100000000, 99616418012871, 100001502370081, 18420682⟩
  ]⟩
]

theorem rangeChecked05 : checkGroups rangeGroups05 = true := by decide +kernel

def rangeGroups : List Group :=
  rangeGroups00 ++ rangeGroups01 ++ rangeGroups02 ++ rangeGroups03 ++ rangeGroups04 ++ rangeGroups05

theorem range_checked : checkGroups rangeGroups = true := by
  simp only [rangeGroups, checkGroups_append, rangeChecked00, rangeChecked01, rangeChecked02, rangeChecked03, rangeChecked04, rangeChecked05, Bool.and_self]

theorem range_linked : linked 55574528 55572198560551 100000000 100001502370081
    (rangeGroups.flatMap Group.blocks) = true := by decide +kernel

theorem range_sound (hTheta : Chebyshev.theta (55574528 : ℝ) ≤ (55572198560551 : ℝ) / 1000000) :
    Chebyshev.theta (100000000 : ℝ) ≤ (100001502370081 : ℝ) / 1000000 ∧
      ∀ n : ℕ, 1000 < n → 55574528 < n → n ≤ 100000000 →
        Chebyshev.psi (n : ℝ) < 1.03883 * (n : ℝ) := by
  simpa only [scale, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    (linked_sound (rangeGroups.flatMap Group.blocks) 55574528 55572198560551 100000000 100001502370081
      (checkGroups_sound rangeGroups range_checked) range_linked
      (by simpa only [scale, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using hTheta))

end OddGoldbachPsi

end OddGoldbachPsiRangeThree

theorem solution :
    Chebyshev.theta (100000000 : ℝ) ≤ (100001502370081 : ℝ) / 1000000 ∧
    ∀ n : ℕ, 55574528 < n → n ≤ 100000000 →
      Chebyshev.psi (n : ℝ) < 1.03883 * (n : ℝ) := by
  have hStart := TaoFivePrimes.rosser_psi_certificate_13631488_to_55574528.1
  obtain ⟨hTheta, hPsi⟩ := OddGoldbachPsiRangeThree.OddGoldbachPsi.range_sound hStart
  exact ⟨hTheta, fun n hn hN => hPsi n (by omega) hn hN⟩

#print axioms solution
