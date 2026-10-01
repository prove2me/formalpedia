-- Prove2me | solution 1 for TaoFivePrimes.rosser_psi_certificate_1_to_13631488
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-24T00:25:43.954766+00:00
-- url     : https://prove2.me/submissions/2ad390fc-63bf-43aa-b9a6-3be75403e2d1

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
  ⟨1, 2, [
    ⟨1, 2, 0, 693149, 693149⟩
  ]⟩,
  ⟨2, 4, [
    ⟨2, 3, 693149, 1791763, 1098614⟩,
    ⟨3, 4, 1791763, 1791763, 1386296⟩
  ]⟩,
  ⟨4, 8, [
    ⟨4, 5, 1791763, 3401202, 1609439⟩,
    ⟨5, 6, 3401202, 3401202, 1791761⟩,
    ⟨6, 7, 3401202, 5347114, 1945912⟩,
    ⟨7, 8, 5347114, 5347114, 2079443⟩
  ]⟩,
  ⟨8, 16, [
    ⟨8, 9, 5347114, 5347114, 2197226⟩,
    ⟨9, 10, 5347114, 5347114, 2302587⟩,
    ⟨10, 11, 5347114, 7745011, 2397897⟩,
    ⟨11, 12, 7745011, 7745011, 2484908⟩,
    ⟨12, 13, 7745011, 10309962, 2564951⟩,
    ⟨13, 14, 10309962, 10309962, 2639059⟩,
    ⟨14, 15, 10309962, 10309962, 2708052⟩,
    ⟨15, 16, 10309962, 10309962, 2772590⟩
  ]⟩,
  ⟨16, 32, [
    ⟨16, 17, 10309962, 13143177, 2833215⟩,
    ⟨17, 18, 13143177, 13143177, 2890373⟩,
    ⟨18, 19, 13143177, 16087617, 2944440⟩,
    ⟨19, 20, 16087617, 16087617, 2995734⟩,
    ⟨20, 21, 16087617, 16087617, 3044524⟩,
    ⟨21, 22, 16087617, 16087617, 3091044⟩,
    ⟨22, 23, 16087617, 19223113, 3135496⟩,
    ⟨23, 24, 19223113, 19223113, 3178055⟩,
    ⟨24, 25, 19223113, 19223113, 3218877⟩,
    ⟨25, 26, 19223113, 19223113, 3258098⟩,
    ⟨26, 27, 19223113, 19223113, 3295838⟩,
    ⟨27, 28, 19223113, 19223113, 3332206⟩,
    ⟨28, 29, 19223113, 22590410, 3367297⟩,
    ⟨29, 30, 22590410, 22590410, 3401199⟩,
    ⟨30, 31, 22590410, 26024399, 3433989⟩,
    ⟨31, 32, 26024399, 26024399, 3465737⟩
  ]⟩,
  ⟨32, 64, [
    ⟨32, 33, 26024399, 26024399, 3496509⟩,
    ⟨33, 34, 26024399, 26024399, 3526362⟩,
    ⟨34, 35, 26024399, 26024399, 3555350⟩,
    ⟨35, 36, 26024399, 26024399, 3583520⟩,
    ⟨36, 37, 26024399, 29635318, 3610919⟩,
    ⟨37, 38, 29635318, 29635318, 3637588⟩,
    ⟨38, 39, 29635318, 29635318, 3663563⟩,
    ⟨39, 40, 29635318, 29635318, 3688881⟩,
    ⟨40, 41, 29635318, 33348892, 3713574⟩,
    ⟨41, 42, 33348892, 33348892, 3737671⟩,
    ⟨42, 43, 33348892, 37110094, 3761202⟩,
    ⟨43, 44, 37110094, 37110094, 3784191⟩,
    ⟨44, 45, 37110094, 37110094, 3806664⟩,
    ⟨45, 46, 37110094, 37110094, 3828643⟩,
    ⟨46, 47, 37110094, 40960243, 3850149⟩,
    ⟨47, 48, 40960243, 40960243, 3871203⟩,
    ⟨48, 49, 40960243, 40960243, 3891822⟩,
    ⟨49, 50, 40960243, 40960243, 3912025⟩,
    ⟨50, 51, 40960243, 40960243, 3931827⟩,
    ⟨51, 52, 40960243, 40960243, 3951245⟩,
    ⟨52, 53, 40960243, 44930536, 3970293⟩,
    ⟨53, 54, 44930536, 44930536, 3988986⟩,
    ⟨54, 55, 44930536, 44930536, 4007335⟩,
    ⟨55, 56, 44930536, 44930536, 4025353⟩,
    ⟨56, 57, 44930536, 44930536, 4043053⟩,
    ⟨57, 58, 44930536, 44930536, 4060445⟩,
    ⟨58, 59, 44930536, 49008075, 4077539⟩,
    ⟨59, 60, 49008075, 49008075, 4094346⟩,
    ⟨60, 61, 49008075, 53118950, 4110875⟩,
    ⟨61, 62, 53118950, 53118950, 4127136⟩,
    ⟨62, 63, 53118950, 53118950, 4143136⟩,
    ⟨63, 64, 53118950, 53118950, 4158885⟩
  ]⟩,
  ⟨64, 128, [
    ⟨64, 65, 53118950, 53118950, 4174389⟩,
    ⟨65, 66, 53118950, 53118950, 4189656⟩,
    ⟨66, 67, 53118950, 57323644, 4204694⟩,
    ⟨67, 68, 57323644, 57323644, 4219509⟩,
    ⟨68, 69, 57323644, 57323644, 4234108⟩,
    ⟨69, 70, 57323644, 57323644, 4248497⟩,
    ⟨70, 71, 57323644, 61586325, 4262681⟩,
    ⟨71, 72, 61586325, 61586325, 4276668⟩,
    ⟨72, 73, 61586325, 65876786, 4290461⟩,
    ⟨73, 74, 65876786, 65876786, 4304067⟩,
    ⟨74, 75, 65876786, 65876786, 4317490⟩,
    ⟨75, 76, 65876786, 65876786, 4330735⟩,
    ⟨76, 77, 65876786, 65876786, 4343807⟩,
    ⟨77, 78, 65876786, 65876786, 4356710⟩,
    ⟨78, 79, 65876786, 70246235, 4369449⟩,
    ⟨79, 80, 70246235, 70246235, 4382028⟩,
    ⟨80, 81, 70246235, 70246235, 4394451⟩,
    ⟨81, 82, 70246235, 70246235, 4406721⟩,
    ⟨82, 83, 70246235, 74665077, 4418842⟩,
    ⟨83, 84, 74665077, 74665077, 4430818⟩,
    ⟨84, 85, 74665077, 74665077, 4442653⟩,
    ⟨85, 86, 74665077, 74665077, 4454349⟩,
    ⟨86, 87, 74665077, 74665077, 4465910⟩,
    ⟨87, 88, 74665077, 74665077, 4477338⟩,
    ⟨88, 89, 74665077, 79153715, 4488638⟩,
    ⟨89, 90, 79153715, 79153715, 4499811⟩,
    ⟨90, 91, 79153715, 79153715, 4510861⟩,
    ⟨91, 92, 79153715, 79153715, 4521790⟩,
    ⟨92, 93, 79153715, 79153715, 4532601⟩,
    ⟨93, 94, 79153715, 79153715, 4543296⟩,
    ⟨94, 95, 79153715, 79153715, 4553878⟩,
    ⟨95, 96, 79153715, 79153715, 4564350⟩,
    ⟨96, 97, 79153715, 83728427, 4574712⟩,
    ⟨97, 98, 83728427, 83728427, 4584969⟩,
    ⟨98, 99, 83728427, 83728427, 4595121⟩,
    ⟨99, 100, 83728427, 83728427, 4605172⟩,
    ⟨100, 101, 83728427, 88343549, 4615122⟩,
    ⟨101, 102, 88343549, 88343549, 4624974⟩,
    ⟨102, 103, 88343549, 92978279, 4634730⟩,
    ⟨103, 104, 92978279, 92978279, 4644392⟩,
    ⟨104, 105, 92978279, 92978279, 4653962⟩,
    ⟨105, 106, 92978279, 92978279, 4663441⟩,
    ⟨106, 107, 92978279, 97651109, 4672830⟩,
    ⟨107, 108, 97651109, 97651109, 4682133⟩,
    ⟨108, 109, 97651109, 102342458, 4691349⟩,
    ⟨109, 110, 102342458, 102342458, 4700482⟩,
    ⟨110, 111, 102342458, 102342458, 4709532⟩,
    ⟨111, 112, 102342458, 102342458, 4718500⟩,
    ⟨112, 113, 102342458, 107069847, 4727389⟩,
    ⟨113, 114, 107069847, 107069847, 4736200⟩,
    ⟨114, 115, 107069847, 107069847, 4744934⟩,
    ⟨115, 116, 107069847, 107069847, 4753592⟩,
    ⟨116, 117, 107069847, 107069847, 4762175⟩,
    ⟨117, 118, 107069847, 107069847, 4770686⟩,
    ⟨118, 119, 107069847, 107069847, 4779125⟩,
    ⟨119, 120, 107069847, 107069847, 4787493⟩,
    ⟨120, 121, 107069847, 107069847, 4795792⟩,
    ⟨121, 122, 107069847, 107069847, 4804023⟩,
    ⟨122, 123, 107069847, 107069847, 4812186⟩,
    ⟨123, 124, 107069847, 107069847, 4820283⟩,
    ⟨124, 125, 107069847, 107069847, 4828315⟩,
    ⟨125, 126, 107069847, 107069847, 4836283⟩,
    ⟨126, 127, 107069847, 111914036, 4844189⟩,
    ⟨127, 128, 111914036, 111914036, 4852032⟩
  ]⟩,
  ⟨128, 256, [
    ⟨128, 129, 111914036, 111914036, 4859814⟩,
    ⟨129, 130, 111914036, 111914036, 4867536⟩,
    ⟨130, 131, 111914036, 116789235, 4875199⟩,
    ⟨131, 132, 116789235, 116789235, 4882803⟩,
    ⟨132, 133, 116789235, 116789235, 4890351⟩,
    ⟨133, 134, 116789235, 116789235, 4897841⟩,
    ⟨134, 135, 116789235, 116789235, 4905276⟩,
    ⟨135, 136, 116789235, 116789235, 4912656⟩,
    ⟨136, 137, 116789235, 121709217, 4919982⟩,
    ⟨137, 138, 121709217, 121709217, 4927255⟩,
    ⟨138, 139, 121709217, 126643692, 4934475⟩,
    ⟨139, 140, 126643692, 126643692, 4941644⟩,
    ⟨140, 141, 126643692, 126643692, 4948761⟩,
    ⟨141, 142, 126643692, 126643692, 4955829⟩,
    ⟨142, 143, 126643692, 126643692, 4962846⟩,
    ⟨143, 144, 126643692, 126643692, 4969815⟩,
    ⟨144, 145, 126643692, 126643692, 4976735⟩,
    ⟨145, 146, 126643692, 126643692, 4983608⟩,
    ⟨146, 147, 126643692, 126643692, 4990434⟩,
    ⟨147, 148, 126643692, 126643692, 4997214⟩,
    ⟨148, 149, 126643692, 131647640, 5003948⟩,
    ⟨149, 150, 131647640, 131647640, 5010637⟩,
    ⟨150, 151, 131647640, 136664921, 5017281⟩,
    ⟨151, 152, 136664921, 136664921, 5023882⟩,
    ⟨152, 153, 136664921, 136664921, 5030439⟩,
    ⟨153, 154, 136664921, 136664921, 5036954⟩,
    ⟨154, 155, 136664921, 136664921, 5043427⟩,
    ⟨155, 156, 136664921, 136664921, 5049858⟩,
    ⟨156, 157, 136664921, 141721168, 5056247⟩,
    ⟨157, 158, 141721168, 141721168, 5062597⟩,
    ⟨158, 159, 141721168, 141721168, 5068906⟩,
    ⟨159, 160, 141721168, 141721168, 5075175⟩,
    ⟨160, 161, 141721168, 141721168, 5081406⟩,
    ⟨161, 162, 141721168, 141721168, 5087598⟩,
    ⟨162, 163, 141721168, 146814920, 5093752⟩,
    ⟨163, 164, 146814920, 146814920, 5099868⟩,
    ⟨164, 165, 146814920, 146814920, 5105947⟩,
    ⟨165, 166, 146814920, 146814920, 5111989⟩,
    ⟨166, 167, 146814920, 151932915, 5117995⟩,
    ⟨167, 168, 151932915, 151932915, 5123965⟩,
    ⟨168, 169, 151932915, 151932915, 5129900⟩,
    ⟨169, 170, 151932915, 151932915, 5135800⟩,
    ⟨170, 171, 151932915, 151932915, 5141665⟩,
    ⟨171, 172, 151932915, 151932915, 5147496⟩,
    ⟨172, 173, 151932915, 157086208, 5153293⟩,
    ⟨173, 174, 157086208, 157086208, 5159057⟩,
    ⟨174, 175, 157086208, 157086208, 5164787⟩,
    ⟨175, 176, 157086208, 157086208, 5170485⟩,
    ⟨176, 177, 157086208, 157086208, 5176151⟩,
    ⟨177, 178, 157086208, 157086208, 5181785⟩,
    ⟨178, 179, 157086208, 162273595, 5187387⟩,
    ⟨179, 180, 162273595, 162273595, 5192958⟩,
    ⟨180, 181, 162273595, 167472094, 5198499⟩,
    ⟨181, 182, 167472094, 167472094, 5204008⟩,
    ⟨182, 183, 167472094, 167472094, 5209488⟩,
    ⟨183, 184, 167472094, 167472094, 5214937⟩,
    ⟨184, 185, 167472094, 167472094, 5220357⟩,
    ⟨185, 186, 167472094, 167472094, 5225748⟩,
    ⟨186, 187, 167472094, 167472094, 5231110⟩,
    ⟨187, 188, 167472094, 167472094, 5236443⟩,
    ⟨188, 189, 167472094, 167472094, 5241749⟩,
    ⟨189, 190, 167472094, 167472094, 5247026⟩,
    ⟨190, 191, 167472094, 172724369, 5252275⟩,
    ⟨191, 192, 172724369, 172724369, 5257497⟩,
    ⟨192, 193, 172724369, 177987061, 5262692⟩,
    ⟨193, 194, 177987061, 177987061, 5267860⟩,
    ⟨194, 195, 177987061, 177987061, 5273001⟩,
    ⟨195, 196, 177987061, 177987061, 5278116⟩,
    ⟨196, 197, 177987061, 183270266, 5283205⟩,
    ⟨197, 198, 183270266, 183270266, 5288269⟩,
    ⟨198, 199, 183270266, 188563572, 5293306⟩,
    ⟨199, 200, 188563572, 188563572, 5298319⟩,
    ⟨200, 201, 188563572, 188563572, 5303306⟩,
    ⟨201, 202, 188563572, 188563572, 5308269⟩,
    ⟨202, 203, 188563572, 188563572, 5313207⟩,
    ⟨203, 204, 188563572, 188563572, 5318121⟩,
    ⟨204, 205, 188563572, 188563572, 5323011⟩,
    ⟨205, 206, 188563572, 188563572, 5327878⟩,
    ⟨206, 207, 188563572, 188563572, 5332720⟩,
    ⟨207, 208, 188563572, 188563572, 5337540⟩,
    ⟨208, 209, 188563572, 188563572, 5342336⟩,
    ⟨209, 210, 188563572, 188563572, 5347109⟩,
    ⟨210, 211, 188563572, 193915432, 5351860⟩,
    ⟨211, 212, 193915432, 193915432, 5356588⟩,
    ⟨212, 213, 193915432, 193915432, 5361294⟩,
    ⟨213, 214, 193915432, 193915432, 5365978⟩,
    ⟨214, 215, 193915432, 193915432, 5370640⟩,
    ⟨215, 216, 193915432, 193915432, 5375280⟩,
    ⟨216, 217, 193915432, 193915432, 5379899⟩,
    ⟨217, 218, 193915432, 193915432, 5384497⟩,
    ⟨218, 219, 193915432, 193915432, 5389073⟩,
    ⟨219, 220, 193915432, 193915432, 5393629⟩,
    ⟨220, 221, 193915432, 193915432, 5398164⟩,
    ⟨221, 222, 193915432, 193915432, 5402679⟩,
    ⟨222, 223, 193915432, 199322605, 5407173⟩,
    ⟨223, 224, 199322605, 199322605, 5411648⟩,
    ⟨224, 225, 199322605, 199322605, 5416102⟩,
    ⟨225, 226, 199322605, 199322605, 5420536⟩,
    ⟨226, 227, 199322605, 204747557, 5424952⟩,
    ⟨227, 228, 204747557, 204747557, 5429347⟩,
    ⟨228, 229, 204747557, 210181281, 5433724⟩,
    ⟨229, 230, 210181281, 210181281, 5438081⟩,
    ⟨230, 231, 210181281, 210181281, 5442419⟩,
    ⟨231, 232, 210181281, 210181281, 5446739⟩,
    ⟨232, 233, 210181281, 215632321, 5451040⟩,
    ⟨233, 234, 215632321, 215632321, 5455323⟩,
    ⟨234, 235, 215632321, 215632321, 5459587⟩,
    ⟨235, 236, 215632321, 215632321, 5463833⟩,
    ⟨236, 237, 215632321, 215632321, 5468062⟩,
    ⟨237, 238, 215632321, 215632321, 5472272⟩,
    ⟨238, 239, 215632321, 221108786, 5476465⟩,
    ⟨239, 240, 221108786, 221108786, 5480640⟩,
    ⟨240, 241, 221108786, 226593584, 5484798⟩,
    ⟨241, 242, 226593584, 226593584, 5488939⟩,
    ⟨242, 243, 226593584, 226593584, 5493063⟩,
    ⟨243, 244, 226593584, 226593584, 5497170⟩,
    ⟨244, 245, 226593584, 226593584, 5501260⟩,
    ⟨245, 246, 226593584, 226593584, 5505333⟩,
    ⟨246, 247, 226593584, 226593584, 5509390⟩,
    ⟨247, 248, 226593584, 226593584, 5513430⟩,
    ⟨248, 249, 226593584, 226593584, 5517454⟩,
    ⟨249, 250, 226593584, 226593584, 5521462⟩,
    ⟨250, 251, 226593584, 232119038, 5525454⟩,
    ⟨251, 252, 232119038, 232119038, 5529431⟩,
    ⟨252, 253, 232119038, 232119038, 5533391⟩,
    ⟨253, 254, 232119038, 232119038, 5537336⟩,
    ⟨254, 255, 232119038, 232119038, 5541265⟩,
    ⟨255, 256, 232119038, 232119038, 5545179⟩
  ]⟩
]

theorem rangeChecked00 : checkGroups rangeGroups00 = true := by decide +kernel

def rangeGroups01 : List Group := [
  ⟨256, 512, [
    ⟨256, 257, 232119038, 237668116, 5549078⟩,
    ⟨257, 258, 237668116, 237668116, 5552961⟩,
    ⟨258, 259, 237668116, 237668116, 5556830⟩,
    ⟨259, 260, 237668116, 237668116, 5560683⟩,
    ⟨260, 261, 237668116, 237668116, 5564522⟩,
    ⟨261, 262, 237668116, 237668116, 5568346⟩,
    ⟨262, 263, 237668116, 243240272, 5572156⟩,
    ⟨263, 264, 243240272, 243240272, 5575951⟩,
    ⟨264, 265, 243240272, 243240272, 5579731⟩,
    ⟨265, 266, 243240272, 243240272, 5583498⟩,
    ⟨266, 267, 243240272, 243240272, 5587250⟩,
    ⟨267, 268, 243240272, 243240272, 5590988⟩,
    ⟨268, 269, 243240272, 248834985, 5594713⟩,
    ⟨269, 270, 248834985, 248834985, 5598423⟩,
    ⟨270, 271, 248834985, 254437105, 5602120⟩,
    ⟨271, 272, 254437105, 254437105, 5605804⟩,
    ⟨272, 273, 254437105, 254437105, 5609473⟩,
    ⟨273, 274, 254437105, 254437105, 5613130⟩,
    ⟨274, 275, 254437105, 254437105, 5616773⟩,
    ⟨275, 276, 254437105, 254437105, 5620402⟩,
    ⟨276, 277, 254437105, 260061124, 5624019⟩,
    ⟨277, 278, 260061124, 260061124, 5627623⟩,
    ⟨278, 279, 260061124, 260061124, 5631213⟩,
    ⟨279, 280, 260061124, 260061124, 5634791⟩,
    ⟨280, 281, 260061124, 265699480, 5638356⟩,
    ⟨281, 282, 265699480, 265699480, 5641909⟩,
    ⟨282, 283, 265699480, 271344928, 5645448⟩,
    ⟨283, 284, 271344928, 271344928, 5648976⟩,
    ⟨284, 285, 271344928, 271344928, 5652491⟩,
    ⟨285, 286, 271344928, 271344928, 5655993⟩,
    ⟨286, 287, 271344928, 271344928, 5659484⟩,
    ⟨287, 288, 271344928, 271344928, 5662962⟩,
    ⟨288, 289, 271344928, 271344928, 5666428⟩,
    ⟨289, 290, 271344928, 271344928, 5669882⟩,
    ⟨290, 291, 271344928, 271344928, 5673325⟩,
    ⟨291, 292, 271344928, 271344928, 5676755⟩,
    ⟨292, 293, 271344928, 277025102, 5680174⟩,
    ⟨293, 294, 277025102, 277025102, 5683581⟩,
    ⟨294, 295, 277025102, 277025102, 5686977⟩,
    ⟨295, 296, 277025102, 277025102, 5690361⟩,
    ⟨296, 297, 277025102, 277025102, 5693734⟩,
    ⟨297, 298, 277025102, 277025102, 5697095⟩,
    ⟨298, 299, 277025102, 277025102, 5700445⟩,
    ⟨299, 300, 277025102, 277025102, 5703784⟩,
    ⟨300, 301, 277025102, 277025102, 5707112⟩,
    ⟨301, 302, 277025102, 277025102, 5710429⟩,
    ⟨302, 303, 277025102, 277025102, 5713734⟩,
    ⟨303, 304, 277025102, 277025102, 5717029⟩,
    ⟨304, 305, 277025102, 277025102, 5720313⟩,
    ⟨305, 306, 277025102, 277025102, 5723587⟩,
    ⟨306, 307, 277025102, 282751951, 5726849⟩,
    ⟨307, 308, 282751951, 282751951, 5730101⟩,
    ⟨308, 309, 282751951, 282751951, 5733343⟩,
    ⟨309, 310, 282751951, 282751951, 5736574⟩,
    ⟨310, 311, 282751951, 288491745, 5739794⟩,
    ⟨311, 312, 288491745, 288491745, 5743005⟩,
    ⟨312, 313, 288491745, 294237950, 5746205⟩,
    ⟨313, 314, 294237950, 294237950, 5749394⟩,
    ⟨314, 315, 294237950, 294237950, 5752574⟩,
    ⟨315, 316, 294237950, 294237950, 5755744⟩,
    ⟨316, 317, 294237950, 299996853, 5758903⟩,
    ⟨317, 318, 299996853, 299996853, 5762053⟩,
    ⟨318, 319, 299996853, 299996853, 5765193⟩,
    ⟨319, 320, 299996853, 299996853, 5768322⟩,
    ⟨320, 321, 299996853, 299996853, 5771443⟩,
    ⟨321, 322, 299996853, 299996853, 5774553⟩,
    ⟨322, 323, 299996853, 299996853, 5777654⟩,
    ⟨323, 324, 299996853, 299996853, 5780745⟩,
    ⟨324, 325, 299996853, 299996853, 5783827⟩,
    ⟨325, 326, 299996853, 299996853, 5786899⟩,
    ⟨326, 327, 299996853, 299996853, 5789962⟩,
    ⟨327, 328, 299996853, 299996853, 5793015⟩,
    ⟨328, 329, 299996853, 299996853, 5796059⟩,
    ⟨329, 330, 299996853, 299996853, 5799094⟩,
    ⟨330, 331, 299996853, 305798973, 5802120⟩,
    ⟨331, 332, 305798973, 305798973, 5805136⟩,
    ⟨332, 333, 305798973, 305798973, 5808144⟩,
    ⟨333, 334, 305798973, 305798973, 5811142⟩,
    ⟨334, 335, 305798973, 305798973, 5814132⟩,
    ⟨335, 336, 305798973, 305798973, 5817113⟩,
    ⟨336, 337, 305798973, 311619057, 5820084⟩,
    ⟨337, 338, 311619057, 311619057, 5823047⟩,
    ⟨338, 339, 311619057, 311619057, 5826002⟩,
    ⟨339, 340, 311619057, 311619057, 5828947⟩,
    ⟨340, 341, 311619057, 311619057, 5831884⟩,
    ⟨341, 342, 311619057, 311619057, 5834812⟩,
    ⟨342, 343, 311619057, 311619057, 5837732⟩,
    ⟨343, 344, 311619057, 311619057, 5840643⟩,
    ⟨344, 345, 311619057, 311619057, 5843546⟩,
    ⟨345, 346, 311619057, 311619057, 5846440⟩,
    ⟨346, 347, 311619057, 317468383, 5849326⟩,
    ⟨347, 348, 317468383, 317468383, 5852204⟩,
    ⟨348, 349, 317468383, 323323456, 5855073⟩,
    ⟨349, 350, 323323456, 323323456, 5857935⟩,
    ⟨350, 351, 323323456, 323323456, 5860788⟩,
    ⟨351, 352, 323323456, 323323456, 5863633⟩,
    ⟨352, 353, 323323456, 329189926, 5866470⟩,
    ⟨353, 354, 329189926, 329189926, 5869298⟩,
    ⟨354, 355, 329189926, 329189926, 5872119⟩,
    ⟨355, 356, 329189926, 329189926, 5874932⟩,
    ⟨356, 357, 329189926, 329189926, 5877737⟩,
    ⟨357, 358, 329189926, 329189926, 5880534⟩,
    ⟨358, 359, 329189926, 335073250, 5883324⟩,
    ⟨359, 360, 335073250, 335073250, 5886106⟩,
    ⟨360, 361, 335073250, 335073250, 5888879⟩,
    ⟨361, 362, 335073250, 335073250, 5891646⟩,
    ⟨362, 363, 335073250, 335073250, 5894404⟩,
    ⟨363, 364, 335073250, 335073250, 5897155⟩,
    ⟨364, 365, 335073250, 335073250, 5899899⟩,
    ⟨365, 366, 335073250, 335073250, 5902635⟩,
    ⟨366, 367, 335073250, 340978613, 5905363⟩,
    ⟨367, 368, 340978613, 340978613, 5908084⟩,
    ⟨368, 369, 340978613, 340978613, 5910798⟩,
    ⟨369, 370, 340978613, 340978613, 5913505⟩,
    ⟨370, 371, 340978613, 340978613, 5916204⟩,
    ⟨371, 372, 340978613, 340978613, 5918895⟩,
    ⟨372, 373, 340978613, 346900193, 5921580⟩,
    ⟨373, 374, 346900193, 346900193, 5924257⟩,
    ⟨374, 375, 346900193, 346900193, 5926928⟩,
    ⟨375, 376, 346900193, 346900193, 5929591⟩,
    ⟨376, 377, 346900193, 346900193, 5932247⟩,
    ⟨377, 378, 346900193, 346900193, 5934896⟩,
    ⟨378, 379, 346900193, 352837731, 5937538⟩,
    ⟨379, 380, 352837731, 352837731, 5940173⟩,
    ⟨380, 381, 352837731, 352837731, 5942801⟩,
    ⟨381, 382, 352837731, 352837731, 5945422⟩,
    ⟨382, 383, 352837731, 358785767, 5948036⟩,
    ⟨383, 384, 358785767, 358785767, 5950644⟩,
    ⟨384, 385, 358785767, 358785767, 5953245⟩,
    ⟨385, 386, 358785767, 358785767, 5955839⟩,
    ⟨386, 387, 358785767, 358785767, 5958426⟩,
    ⟨387, 388, 358785767, 358785767, 5961007⟩,
    ⟨388, 389, 358785767, 364749348, 5963581⟩,
    ⟨389, 390, 364749348, 364749348, 5966148⟩,
    ⟨390, 391, 364749348, 364749348, 5968709⟩,
    ⟨391, 392, 364749348, 364749348, 5971263⟩,
    ⟨392, 393, 364749348, 364749348, 5973811⟩,
    ⟨393, 394, 364749348, 364749348, 5976352⟩,
    ⟨394, 395, 364749348, 364749348, 5978887⟩,
    ⟨395, 396, 364749348, 364749348, 5981416⟩,
    ⟨396, 397, 364749348, 370733286, 5983938⟩,
    ⟨397, 398, 370733286, 370733286, 5986454⟩,
    ⟨398, 399, 370733286, 370733286, 5988963⟩,
    ⟨399, 400, 370733286, 370733286, 5991466⟩,
    ⟨400, 402, 370733286, 376729740, 5996454⟩,
    ⟨402, 404, 376729740, 376729740, 6001416⟩,
    ⟨404, 406, 376729740, 376729740, 6006355⟩,
    ⟨406, 408, 376729740, 376729740, 6011269⟩,
    ⟨408, 410, 376729740, 382745899, 6016159⟩,
    ⟨410, 412, 382745899, 382745899, 6021025⟩,
    ⟨412, 414, 382745899, 382745899, 6025867⟩,
    ⟨414, 416, 382745899, 382745899, 6030687⟩,
    ⟨416, 418, 382745899, 382745899, 6035483⟩,
    ⟨418, 420, 382745899, 388786155, 6040256⟩,
    ⟨420, 422, 388786155, 394831162, 6045007⟩,
    ⟨422, 424, 394831162, 394831162, 6049735⟩,
    ⟨424, 426, 394831162, 394831162, 6054441⟩,
    ⟨426, 428, 394831162, 394831162, 6059125⟩,
    ⟨428, 430, 394831162, 394831162, 6063787⟩,
    ⟨430, 432, 394831162, 400899589, 6068427⟩,
    ⟨432, 434, 400899589, 406972635, 6073046⟩,
    ⟨434, 436, 406972635, 406972635, 6077644⟩,
    ⟨436, 438, 406972635, 406972635, 6082220⟩,
    ⟨438, 440, 406972635, 413059411, 6086776⟩,
    ⟨440, 442, 413059411, 413059411, 6091311⟩,
    ⟨442, 444, 413059411, 419155237, 6095826⟩,
    ⟨444, 446, 419155237, 419155237, 6100320⟩,
    ⟨446, 448, 419155237, 419155237, 6104795⟩,
    ⟨448, 450, 419155237, 425264486, 6109249⟩,
    ⟨450, 452, 425264486, 425264486, 6113684⟩,
    ⟨452, 454, 425264486, 425264486, 6118099⟩,
    ⟨454, 456, 425264486, 425264486, 6122494⟩,
    ⟨456, 458, 425264486, 431391357, 6126871⟩,
    ⟨458, 460, 431391357, 431391357, 6131228⟩,
    ⟨460, 462, 431391357, 437526923, 6135566⟩,
    ⟨462, 464, 437526923, 443666809, 6139886⟩,
    ⟨464, 466, 443666809, 443666809, 6144187⟩,
    ⟨466, 468, 443666809, 449815279, 6148470⟩,
    ⟨468, 470, 449815279, 449815279, 6152734⟩,
    ⟨470, 472, 449815279, 449815279, 6156980⟩,
    ⟨472, 474, 449815279, 449815279, 6161209⟩,
    ⟨474, 476, 449815279, 449815279, 6165419⟩,
    ⟨476, 478, 449815279, 449815279, 6169612⟩,
    ⟨478, 480, 449815279, 455989067, 6173788⟩,
    ⟨480, 482, 455989067, 455989067, 6177946⟩,
    ⟨482, 484, 455989067, 455989067, 6182086⟩,
    ⟨484, 486, 455989067, 455989067, 6186210⟩,
    ⟨486, 488, 455989067, 462179384, 6190317⟩,
    ⟨488, 490, 462179384, 462179384, 6194407⟩,
    ⟨490, 492, 462179384, 468377864, 6198480⟩,
    ⟨492, 494, 468377864, 468377864, 6202537⟩,
    ⟨494, 496, 468377864, 468377864, 6206577⟩,
    ⟨496, 498, 468377864, 468377864, 6210602⟩,
    ⟨498, 500, 468377864, 474592474, 6214610⟩,
    ⟨500, 502, 474592474, 474592474, 6218602⟩,
    ⟨502, 504, 474592474, 480815052, 6222578⟩,
    ⟨504, 506, 480815052, 480815052, 6226538⟩,
    ⟨506, 508, 480815052, 480815052, 6230483⟩,
    ⟨508, 510, 480815052, 487049464, 6234412⟩,
    ⟨510, 512, 487049464, 487049464, 6238326⟩
  ]⟩,
  ⟨512, 1024, [
    ⟨512, 514, 487049464, 487049464, 6242225⟩,
    ⟨514, 516, 487049464, 487049464, 6246108⟩,
    ⟨516, 518, 487049464, 487049464, 6249977⟩,
    ⟨518, 520, 487049464, 487049464, 6253830⟩,
    ⟨520, 522, 487049464, 493307133, 6257669⟩,
    ⟨522, 524, 493307133, 499568626, 6261493⟩,
    ⟨524, 526, 499568626, 499568626, 6265303⟩,
    ⟨526, 528, 499568626, 499568626, 6269098⟩,
    ⟨528, 530, 499568626, 499568626, 6272879⟩,
    ⟨530, 532, 499568626, 499568626, 6276645⟩,
    ⟨532, 534, 499568626, 499568626, 6280397⟩,
    ⟨534, 536, 499568626, 499568626, 6284136⟩,
    ⟨536, 538, 499568626, 499568626, 6287860⟩,
    ⟨538, 540, 499568626, 499568626, 6291571⟩,
    ⟨540, 542, 499568626, 505863894, 6295268⟩,
    ⟨542, 544, 505863894, 505863894, 6298951⟩,
    ⟨544, 546, 505863894, 505863894, 6302620⟩,
    ⟨546, 548, 505863894, 512170171, 6306277⟩,
    ⟨548, 550, 512170171, 512170171, 6309920⟩,
    ⟨550, 552, 512170171, 512170171, 6313550⟩,
    ⟨552, 554, 512170171, 512170171, 6317166⟩,
    ⟨554, 556, 512170171, 512170171, 6320770⟩,
    ⟨556, 558, 512170171, 518494531, 6324360⟩,
    ⟨558, 560, 518494531, 518494531, 6327938⟩,
    ⟨560, 562, 518494531, 518494531, 6331503⟩,
    ⟨562, 564, 518494531, 524829587, 6335056⟩,
    ⟨564, 566, 524829587, 524829587, 6338596⟩,
    ⟨566, 568, 524829587, 524829587, 6342123⟩,
    ⟨568, 570, 524829587, 531175225, 6345638⟩,
    ⟨570, 572, 531175225, 537524365, 6349140⟩,
    ⟨572, 574, 537524365, 537524365, 6352631⟩,
    ⟨574, 576, 537524365, 537524365, 6356109⟩,
    ⟨576, 578, 537524365, 543883940, 6359575⟩,
    ⟨578, 580, 543883940, 543883940, 6363030⟩,
    ⟨580, 582, 543883940, 543883940, 6366472⟩,
    ⟨582, 584, 543883940, 543883940, 6369902⟩,
    ⟨584, 586, 543883940, 543883940, 6373321⟩,
    ⟨586, 588, 543883940, 550260668, 6376728⟩,
    ⟨588, 590, 550260668, 550260668, 6380124⟩,
    ⟨590, 592, 550260668, 550260668, 6383508⟩,
    ⟨592, 594, 550260668, 556647549, 6386881⟩,
    ⟨594, 596, 556647549, 556647549, 6390242⟩,
    ⟨596, 598, 556647549, 556647549, 6393592⟩,
    ⟨598, 600, 556647549, 563044480, 6396931⟩,
    ⟨600, 603, 563044480, 569446399, 6401919⟩,
    ⟨603, 606, 569446399, 569446399, 6406881⟩,
    ⟨606, 609, 569446399, 575858219, 6411820⟩,
    ⟨609, 612, 575858219, 575858219, 6416734⟩,
    ⟨612, 615, 575858219, 582279843, 6421624⟩,
    ⟨615, 618, 582279843, 588706333, 6426490⟩,
    ⟨618, 621, 588706333, 595137666, 6431333⟩,
    ⟨621, 624, 595137666, 595137666, 6436152⟩,
    ⟨624, 627, 595137666, 595137666, 6440948⟩,
    ⟨627, 630, 595137666, 595137666, 6445721⟩,
    ⟨630, 633, 595137666, 601588138, 6450472⟩,
    ⟨633, 636, 601588138, 601588138, 6455200⟩,
    ⟨636, 639, 601588138, 601588138, 6459906⟩,
    ⟨639, 642, 601588138, 608052728, 6464590⟩,
    ⟨642, 645, 608052728, 614521980, 6469252⟩,
    ⟨645, 648, 614521980, 620995872, 6473892⟩,
    ⟨648, 651, 620995872, 620995872, 6478511⟩,
    ⟨651, 654, 620995872, 627478981, 6483109⟩,
    ⟨654, 657, 627478981, 627478981, 6487686⟩,
    ⟨657, 660, 627478981, 633971222, 6492241⟩,
    ⟨660, 663, 633971222, 640467998, 6496776⟩,
    ⟨663, 666, 640467998, 640467998, 6501291⟩,
    ⟨666, 669, 640467998, 640467998, 6505786⟩,
    ⟨669, 672, 640467998, 640467998, 6510260⟩,
    ⟨672, 675, 640467998, 646982712, 6514714⟩,
    ⟨675, 678, 646982712, 653501861, 6519149⟩,
    ⟨678, 681, 653501861, 653501861, 6523564⟩,
    ⟨681, 684, 653501861, 660029820, 6527959⟩,
    ⟨684, 687, 660029820, 660029820, 6532336⟩,
    ⟨687, 690, 660029820, 660029820, 6536693⟩,
    ⟨690, 693, 660029820, 666570851, 6541031⟩,
    ⟨693, 696, 666570851, 666570851, 6545351⟩,
    ⟨696, 699, 666570851, 666570851, 6549652⟩,
    ⟨699, 702, 666570851, 673124786, 6553935⟩,
    ⟨702, 705, 673124786, 673124786, 6558199⟩,
    ⟨705, 708, 673124786, 673124786, 6562446⟩,
    ⟨708, 711, 673124786, 679691460, 6566674⟩,
    ⟨711, 714, 679691460, 679691460, 6570884⟩,
    ⟨714, 717, 679691460, 679691460, 6575077⟩,
    ⟨717, 720, 679691460, 686270713, 6579253⟩,
    ⟨720, 723, 686270713, 686270713, 6583411⟩,
    ⟨723, 726, 686270713, 686270713, 6587552⟩,
    ⟨726, 729, 686270713, 692862388, 6591675⟩,
    ⟨729, 732, 692862388, 692862388, 6595782⟩,
    ⟨732, 735, 692862388, 699462260, 6599872⟩,
    ⟨735, 738, 699462260, 699462260, 6603945⟩,
    ⟨738, 741, 699462260, 706070262, 6608002⟩,
    ⟨741, 744, 706070262, 712682305, 6612043⟩,
    ⟨744, 747, 712682305, 712682305, 6616067⟩,
    ⟨747, 750, 712682305, 712682305, 6620075⟩,
    ⟨750, 753, 712682305, 719306372, 6624067⟩,
    ⟨753, 756, 719306372, 719306372, 6628043⟩,
    ⟨756, 759, 719306372, 725938375, 6632003⟩,
    ⟨759, 762, 725938375, 732574323, 6635948⟩,
    ⟨762, 765, 732574323, 732574323, 6639877⟩,
    ⟨765, 768, 732574323, 732574323, 6643791⟩,
    ⟨768, 771, 732574323, 739222013, 6647690⟩,
    ⟨771, 774, 739222013, 745873586, 6651573⟩,
    ⟨774, 777, 745873586, 745873586, 6655442⟩,
    ⟨777, 780, 745873586, 745873586, 6659295⟩,
    ⟨780, 783, 745873586, 745873586, 6663134⟩,
    ⟨783, 786, 745873586, 745873586, 6666958⟩,
    ⟨786, 789, 745873586, 752544354, 6670768⟩,
    ⟨789, 792, 752544354, 752544354, 6674563⟩,
    ⟨792, 795, 752544354, 752544354, 6678344⟩,
    ⟨795, 798, 752544354, 759226464, 6682110⟩,
    ⟨798, 801, 759226464, 759226464, 6685862⟩,
    ⟨801, 805, 759226464, 759226464, 6690844⟩,
    ⟨805, 809, 759226464, 765922264, 6695800⟩,
    ⟨809, 813, 765922264, 772622997, 6700733⟩,
    ⟨813, 817, 772622997, 772622997, 6705641⟩,
    ⟨817, 821, 772622997, 779333522, 6710525⟩,
    ⟨821, 825, 779333522, 786048907, 6715385⟩,
    ⟨825, 829, 786048907, 799489351, 6720222⟩,
    ⟨829, 833, 799489351, 799489351, 6725035⟩,
    ⟨833, 837, 799489351, 799489351, 6729826⟩,
    ⟨837, 841, 799489351, 806223944, 6734593⟩,
    ⟨841, 845, 806223944, 806223944, 6739338⟩,
    ⟨845, 849, 806223944, 806223944, 6744061⟩,
    ⟨849, 853, 806223944, 812972705, 6748761⟩,
    ⟨853, 857, 812972705, 819726144, 6753439⟩,
    ⟨857, 861, 819726144, 826484240, 6758096⟩,
    ⟨861, 865, 826484240, 833246971, 6762731⟩,
    ⟨865, 869, 833246971, 833246971, 6767345⟩,
    ⟨869, 873, 833246971, 833246971, 6771937⟩,
    ⟨873, 877, 833246971, 840023479, 6776508⟩,
    ⟨877, 881, 840023479, 846804538, 6781059⟩,
    ⟨881, 885, 846804538, 853590127, 6785589⟩,
    ⟨885, 889, 853590127, 860380226, 6790099⟩,
    ⟨889, 893, 860380226, 860380226, 6794588⟩,
    ⟨893, 897, 860380226, 860380226, 6799057⟩,
    ⟨897, 901, 860380226, 860380226, 6803507⟩,
    ⟨901, 905, 860380226, 860380226, 6807936⟩,
    ⟨905, 909, 860380226, 867192573, 6812347⟩,
    ⟨909, 913, 867192573, 874009310, 6816737⟩,
    ⟨913, 917, 874009310, 874009310, 6821109⟩,
    ⟨917, 921, 874009310, 880834772, 6825462⟩,
    ⟨921, 925, 880834772, 880834772, 6829795⟩,
    ⟨925, 929, 880834772, 887668882, 6834110⟩,
    ⟨929, 933, 887668882, 887668882, 6838407⟩,
    ⟨933, 937, 887668882, 894511567, 6842685⟩,
    ⟨937, 941, 894511567, 901358512, 6846945⟩,
    ⟨941, 945, 901358512, 901358512, 6851186⟩,
    ⟨945, 949, 901358512, 908213922, 6855410⟩,
    ⟨949, 953, 908213922, 915073538, 6859616⟩,
    ⟨953, 957, 915073538, 915073538, 6863805⟩,
    ⟨957, 961, 915073538, 915073538, 6867976⟩,
    ⟨961, 965, 915073538, 915073538, 6872130⟩,
    ⟨965, 969, 915073538, 921949804, 6876266⟩,
    ⟨969, 973, 921949804, 928830190, 6880386⟩,
    ⟨973, 977, 928830190, 935714678, 6884488⟩,
    ⟨977, 981, 935714678, 935714678, 6888574⟩,
    ⟨981, 985, 935714678, 942607321, 6892643⟩,
    ⟨985, 989, 942607321, 942607321, 6896696⟩,
    ⟨989, 993, 942607321, 949508053, 6900732⟩,
    ⟨993, 997, 949508053, 956412805, 6904752⟩,
    ⟨997, 1000, 956412805, 956412805, 6907757⟩,
    ⟨1000, 1005, 956412805, 956412805, 6912744⟩,
    ⟨1005, 1010, 956412805, 963330512, 6917707⟩,
    ⟨1010, 1015, 963330512, 970253157, 6922645⟩,
    ⟨1015, 1020, 970253157, 977180716, 6927559⟩,
    ⟨1020, 1024, 977180716, 984112189, 6931473⟩
  ]⟩,
  ⟨1024, 2048, [
    ⟨1024, 1029, 984112189, 984112189, 6936344⟩,
    ⟨1029, 1034, 984112189, 997994573, 6941192⟩,
    ⟨1034, 1039, 997994573, 1004940588, 6946015⟩,
    ⟨1039, 1044, 1004940588, 1004940588, 6950816⟩,
    ⟨1044, 1049, 1004940588, 1011896182, 6955594⟩,
    ⟨1049, 1054, 1011896182, 1018856531, 6960349⟩,
    ⟨1054, 1059, 1018856531, 1018856531, 6965082⟩,
    ⟨1059, 1064, 1018856531, 1032796115, 6969792⟩,
    ⟨1064, 1069, 1032796115, 1039770595, 6974480⟩,
    ⟨1069, 1074, 1039770595, 1039770595, 6979147⟩,
    ⟨1074, 1079, 1039770595, 1039770595, 6983791⟩,
    ⟨1079, 1084, 1039770595, 1039770595, 6988415⟩,
    ⟨1084, 1089, 1039770595, 1046763612, 6993017⟩,
    ⟨1089, 1094, 1046763612, 1060758806, 6997597⟩,
    ⟨1094, 1099, 1060758806, 1067760963, 7002157⟩,
    ⟨1099, 1104, 1067760963, 1074767660, 7006697⟩,
    ⟨1104, 1109, 1074767660, 1081778875, 7011215⟩,
    ⟨1109, 1114, 1081778875, 1081778875, 7015714⟩,
    ⟨1114, 1119, 1081778875, 1088799067, 7020192⟩,
    ⟨1119, 1124, 1088799067, 1095823718, 7024651⟩,
    ⟨1124, 1129, 1095823718, 1102852807, 7029089⟩,
    ⟨1129, 1134, 1102852807, 1102852807, 7033508⟩,
    ⟨1134, 1139, 1102852807, 1102852807, 7037907⟩,
    ⟨1139, 1144, 1102852807, 1102852807, 7042288⟩,
    ⟨1144, 1149, 1102852807, 1102852807, 7046649⟩,
    ⟨1149, 1154, 1102852807, 1116954789, 7050991⟩,
    ⟨1154, 1159, 1116954789, 1116954789, 7055314⟩,
    ⟨1159, 1164, 1116954789, 1124014408, 7059619⟩,
    ⟨1164, 1169, 1124014408, 1124014408, 7063905⟩,
    ⟨1169, 1174, 1124014408, 1131082582, 7068174⟩,
    ⟨1174, 1179, 1131082582, 1131082582, 7072423⟩,
    ⟨1179, 1184, 1131082582, 1138159237, 7076655⟩,
    ⟨1184, 1189, 1138159237, 1145240106, 7080869⟩,
    ⟨1189, 1194, 1145240106, 1152325172, 7085066⟩,
    ⟨1194, 1199, 1152325172, 1152325172, 7089245⟩,
    ⟨1199, 1204, 1152325172, 1159418578, 7093406⟩,
    ⟨1204, 1210, 1159418578, 1159418578, 7098377⟩,
    ⟨1210, 1216, 1159418578, 1166521902, 7103324⟩,
    ⟨1216, 1222, 1166521902, 1173630148, 7108246⟩,
    ⟨1222, 1228, 1173630148, 1180743292, 7113144⟩,
    ⟨1228, 1234, 1180743292, 1194979328, 7118018⟩,
    ⟨1234, 1240, 1194979328, 1202102196, 7122868⟩,
    ⟨1240, 1246, 1202102196, 1202102196, 7127695⟩,
    ⟨1246, 1252, 1202102196, 1209234695, 7132499⟩,
    ⟨1252, 1258, 1209234695, 1209234695, 7137280⟩,
    ⟨1258, 1264, 1209234695, 1216376733, 7142038⟩,
    ⟨1264, 1270, 1216376733, 1216376733, 7146774⟩,
    ⟨1270, 1276, 1216376733, 1216376733, 7151487⟩,
    ⟨1276, 1282, 1216376733, 1230689089, 7156178⟩,
    ⟨1282, 1288, 1230689089, 1237849936, 7160847⟩,
    ⟨1288, 1294, 1237849936, 1252180926, 7165495⟩,
    ⟨1294, 1300, 1252180926, 1259351047, 7170121⟩,
    ⟨1300, 1306, 1259351047, 1273700499, 7174726⟩,
    ⟨1306, 1312, 1273700499, 1280879808, 7179309⟩,
    ⟨1312, 1318, 1280879808, 1280879808, 7183872⟩,
    ⟨1318, 1324, 1280879808, 1295256636, 7188414⟩,
    ⟨1324, 1330, 1295256636, 1302449572, 7192936⟩,
    ⟨1330, 1336, 1302449572, 1302449572, 7197437⟩,
    ⟨1336, 1342, 1302449572, 1302449572, 7201918⟩,
    ⟨1342, 1348, 1302449572, 1302449572, 7206379⟩,
    ⟨1348, 1354, 1302449572, 1302449572, 7210820⟩,
    ⟨1354, 1360, 1302449572, 1302449572, 7215241⟩,
    ⟨1360, 1366, 1302449572, 1309669216, 7219644⟩,
    ⟨1366, 1372, 1309669216, 1316893242, 7224026⟩,
    ⟨1372, 1378, 1316893242, 1324121632, 7228390⟩,
    ⟨1378, 1384, 1324121632, 1331354367, 7232735⟩,
    ⟨1384, 1390, 1331354367, 1331354367, 7237061⟩,
    ⟨1390, 1396, 1331354367, 1331354367, 7241368⟩,
    ⟨1396, 1402, 1331354367, 1338600024, 7245657⟩,
    ⟨1402, 1409, 1338600024, 1345850661, 7250637⟩,
    ⟨1409, 1416, 1345850661, 1345850661, 7255593⟩,
    ⟨1416, 1423, 1345850661, 1353111185, 7260524⟩,
    ⟨1423, 1430, 1353111185, 1367642047, 7265431⟩,
    ⟨1430, 1437, 1367642047, 1374912361, 7270314⟩,
    ⟨1437, 1444, 1374912361, 1382187535, 7275174⟩,
    ⟨1444, 1451, 1382187535, 1396747555, 7280010⟩,
    ⟨1451, 1458, 1396747555, 1404032377, 7284822⟩,
    ⟨1458, 1465, 1404032377, 1411321989, 7289612⟩,
    ⟨1465, 1472, 1411321989, 1418616368, 7294379⟩,
    ⟨1472, 1479, 1418616368, 1418616368, 7299123⟩,
    ⟨1479, 1486, 1418616368, 1433224058, 7303845⟩,
    ⟨1486, 1493, 1433224058, 1455149690, 7308544⟩,
    ⟨1493, 1500, 1455149690, 1462462912, 7313222⟩,
    ⟨1500, 1507, 1462462912, 1462462912, 7317878⟩,
    ⟨1507, 1514, 1462462912, 1469785424, 7322512⟩,
    ⟨1514, 1521, 1469785424, 1469785424, 7327125⟩,
    ⟨1521, 1528, 1469785424, 1477117140, 7331716⟩,
    ⟨1528, 1535, 1477117140, 1484453427, 7336287⟩,
    ⟨1535, 1542, 1484453427, 1484453427, 7340837⟩,
    ⟨1542, 1549, 1484453427, 1499144159, 7345366⟩,
    ⟨1549, 1556, 1499144159, 1506494034, 7349875⟩,
    ⟨1556, 1563, 1506494034, 1513848398, 7354364⟩,
    ⟨1563, 1570, 1513848398, 1521207230, 7358832⟩,
    ⟨1570, 1577, 1521207230, 1528570511, 7363281⟩,
    ⟨1577, 1584, 1528570511, 1543305931, 7367710⟩,
    ⟨1584, 1591, 1543305931, 1543305931, 7372120⟩,
    ⟨1591, 1598, 1543305931, 1550682441, 7376510⟩,
    ⟨1598, 1605, 1550682441, 1558063322, 7380881⟩,
    ⟨1605, 1613, 1558063322, 1580220881, 7385853⟩,
    ⟨1613, 1621, 1580220881, 1595002481, 7390800⟩,
    ⟨1621, 1629, 1595002481, 1602398204, 7395723⟩,
    ⟨1629, 1637, 1602398204, 1609798826, 7400622⟩,
    ⟨1637, 1645, 1609798826, 1609798826, 7405497⟩,
    ⟨1645, 1653, 1609798826, 1609798826, 7410349⟩,
    ⟨1653, 1661, 1609798826, 1617214003, 7415177⟩,
    ⟨1661, 1669, 1617214003, 1639473946, 7419981⟩,
    ⟨1669, 1677, 1639473946, 1639473946, 7424763⟩,
    ⟨1677, 1685, 1639473946, 1639473946, 7429522⟩,
    ⟨1685, 1693, 1639473946, 1646908205, 7434259⟩,
    ⟨1693, 1701, 1646908205, 1661786151, 7438973⟩,
    ⟨1701, 1709, 1661786151, 1669229816, 7443665⟩,
    ⟨1709, 1717, 1669229816, 1669229816, 7448335⟩,
    ⟨1717, 1725, 1669229816, 1684135784, 7452984⟩,
    ⟨1725, 1733, 1684135784, 1691593395, 7457611⟩,
    ⟨1733, 1741, 1691593395, 1699055611, 7462216⟩,
    ⟨1741, 1749, 1699055611, 1706522412, 7466801⟩,
    ⟨1749, 1757, 1706522412, 1713993777, 7471365⟩,
    ⟨1757, 1765, 1713993777, 1721469684, 7475907⟩,
    ⟨1765, 1773, 1721469684, 1721469684, 7480430⟩,
    ⟨1773, 1781, 1721469684, 1728954616, 7484932⟩,
    ⟨1781, 1789, 1728954616, 1751422858, 7489414⟩,
    ⟨1789, 1797, 1751422858, 1751422858, 7493875⟩,
    ⟨1797, 1805, 1751422858, 1758921175, 7498317⟩,
    ⟨1805, 1814, 1758921175, 1766424466, 7503291⟩,
    ⟨1814, 1823, 1766424466, 1773932706, 7508240⟩,
    ⟨1823, 1832, 1773932706, 1781445871, 7513165⟩,
    ⟨1832, 1841, 1781445871, 1781445871, 7518066⟩,
    ⟨1841, 1850, 1781445871, 1788968813, 7522942⟩,
    ⟨1850, 1859, 1788968813, 1788968813, 7527795⟩,
    ⟨1859, 1868, 1788968813, 1804034063, 7532625⟩,
    ⟨1868, 1877, 1804034063, 1826646359, 7537432⟩,
    ⟨1877, 1886, 1826646359, 1834188574, 7542215⟩,
    ⟨1886, 1895, 1834188574, 1841735550, 7546976⟩,
    ⟨1895, 1904, 1841735550, 1849287264, 7551714⟩,
    ⟨1904, 1913, 1849287264, 1864400122, 7556429⟩,
    ⟨1913, 1922, 1864400122, 1864400122, 7561123⟩,
    ⟨1922, 1931, 1864400122, 1871965917, 7565795⟩,
    ⟨1931, 1940, 1871965917, 1879536362, 7570445⟩,
    ⟨1940, 1949, 1879536362, 1887111435, 7575073⟩,
    ⟨1949, 1958, 1887111435, 1894691115, 7579680⟩,
    ⟨1958, 1967, 1894691115, 1894691115, 7584266⟩,
    ⟨1967, 1976, 1894691115, 1902279946, 7588831⟩,
    ⟨1976, 1985, 1902279946, 1909873322, 7593376⟩,
    ⟨1985, 1994, 1909873322, 1925069120, 7597899⟩,
    ⟨1994, 2003, 1925069120, 1947876329, 7602403⟩,
    ⟨2003, 2013, 1947876329, 1955483712, 7607383⟩,
    ⟨2013, 2023, 1955483712, 1963096050, 7612338⟩,
    ⟨2023, 2033, 1963096050, 1978330588, 7617269⟩,
    ⟨2033, 2043, 1978330588, 1985952764, 7622176⟩,
    ⟨2043, 2048, 1985952764, 1985952764, 7624620⟩
  ]⟩,
  ⟨2048, 4096, [
    ⟨2048, 2058, 1985952764, 1993582255, 7629491⟩,
    ⟨2058, 2068, 1993582255, 2001216594, 7634339⟩,
    ⟨2068, 2078, 2001216594, 2008855757, 7639163⟩,
    ⟨2078, 2088, 2008855757, 2031787646, 7643963⟩,
    ⟨2088, 2098, 2031787646, 2039436387, 7648741⟩,
    ⟨2098, 2108, 2039436387, 2047089883, 7653496⟩,
    ⟨2108, 2118, 2047089883, 2062406341, 7658229⟩,
    ⟨2118, 2128, 2062406341, 2062406341, 7662939⟩,
    ⟨2128, 2138, 2062406341, 2085409225, 7667628⟩,
    ⟨2138, 2148, 2085409225, 2100753813, 7672294⟩,
    ⟨2148, 2158, 2100753813, 2108430752, 7676939⟩,
    ⟨2158, 2168, 2108430752, 2116112314, 7681562⟩,
    ⟨2168, 2178, 2116112314, 2116112314, 7686164⟩,
    ⟨2178, 2188, 2116112314, 2123803059, 7690745⟩,
    ⟨2188, 2198, 2123803059, 2123803059, 7695305⟩,
    ⟨2198, 2208, 2123803059, 2139202747, 7699844⟩,
    ⟨2208, 2219, 2139202747, 2146907560, 7704813⟩,
    ⟨2219, 2230, 2146907560, 2154617318, 7709758⟩,
    ⟨2230, 2241, 2154617318, 2170046676, 7714679⟩,
    ⟨2241, 2252, 2170046676, 2185485826, 7719575⟩,
    ⟨2252, 2263, 2185485826, 2185485826, 7724448⟩,
    ⟨2263, 2274, 2185485826, 2208673717, 7729297⟩,
    ⟨2274, 2285, 2208673717, 2216407840, 7734123⟩,
    ⟨2285, 2296, 2216407840, 2231885690, 7738925⟩,
    ⟨2296, 2307, 2231885690, 2239629395, 7743705⟩,
    ⟨2307, 2318, 2239629395, 2255126319, 7748462⟩,
    ⟨2318, 2329, 2255126319, 2255126319, 7753196⟩,
    ⟨2329, 2340, 2255126319, 2270642135, 7757908⟩,
    ⟨2340, 2351, 2270642135, 2293929929, 7762598⟩,
    ⟨2351, 2362, 2293929929, 2301697194, 7767265⟩,
    ⟨2362, 2373, 2301697194, 2309469106, 7771912⟩,
    ⟨2373, 2384, 2309469106, 2332798717, 7776537⟩,
    ⟨2384, 2395, 2332798717, 2348360997, 7781140⟩,
    ⟨2395, 2406, 2348360997, 2356146719, 7785722⟩,
    ⟨2406, 2418, 2356146719, 2371728115, 7790698⟩,
    ⟨2418, 2430, 2371728115, 2379523763, 7795648⟩,
    ⟨2430, 2442, 2379523763, 2395124911, 7800574⟩,
    ⟨2442, 2454, 2395124911, 2402930387, 7805476⟩,
    ⟨2454, 2466, 2402930387, 2410740741, 7810354⟩,
    ⟨2466, 2478, 2410740741, 2434186368, 7815209⟩,
    ⟨2478, 2490, 2434186368, 2434186368, 7820039⟩,
    ⟨2490, 2502, 2434186368, 2434186368, 7824847⟩,
    ⟨2502, 2514, 2434186368, 2442016000, 7829632⟩,
    ⟨2514, 2526, 2442016000, 2449850394, 7834394⟩,
    ⟨2526, 2538, 2449850394, 2457689527, 7839133⟩,
    ⟨2538, 2550, 2457689527, 2481221077, 7843850⟩,
    ⟨2550, 2562, 2481221077, 2496918167, 7848545⟩,
    ⟨2562, 2574, 2496918167, 2496918167, 7853218⟩,
    ⟨2574, 2586, 2496918167, 2504776036, 7857869⟩,
    ⟨2586, 2598, 2504776036, 2520501034, 7862499⟩,
    ⟨2598, 2610, 2520501034, 2528368141, 7867107⟩,
    ⟨2610, 2623, 2528368141, 2544112291, 7872075⟩,
    ⟨2623, 2636, 2544112291, 2551989310, 7877019⟩,
    ⟨2636, 2649, 2551989310, 2559871249, 7881939⟩,
    ⟨2649, 2662, 2559871249, 2575644917, 7886834⟩,
    ⟨2662, 2675, 2575644917, 2591428329, 7891706⟩,
    ⟨2675, 2688, 2591428329, 2615117991, 7896554⟩,
    ⟨2688, 2701, 2615117991, 2638822128, 7901379⟩,
    ⟨2701, 2714, 2638822128, 2662540668, 7906180⟩,
    ⟨2714, 2727, 2662540668, 2670451627, 7910959⟩,
    ⟨2727, 2740, 2670451627, 2686283057, 7915715⟩,
    ⟨2740, 2753, 2686283057, 2710044401, 7920448⟩,
    ⟨2753, 2766, 2710044401, 2710044401, 7925159⟩,
    ⟨2766, 2779, 2710044401, 2725904097, 7929848⟩,
    ⟨2779, 2792, 2725904097, 2741773127, 7934515⟩,
    ⟨2792, 2805, 2741773127, 2765590607, 7939160⟩,
    ⟨2805, 2819, 2765590607, 2773534746, 7944139⟩,
    ⟨2819, 2833, 2773534746, 2781483839, 7949093⟩,
    ⟨2833, 2847, 2781483839, 2797391885, 7954023⟩,
    ⟨2847, 2861, 2797391885, 2821268669, 7958928⟩,
    ⟨2861, 2875, 2821268669, 2821268669, 7963809⟩,
    ⟨2875, 2889, 2821268669, 2837206003, 7968667⟩,
    ⟨2889, 2903, 2837206003, 2853153005, 7973501⟩,
    ⟨2903, 2917, 2853153005, 2869109629, 7978312⟩,
    ⟨2917, 2931, 2869109629, 2877092729, 7983100⟩,
    ⟨2931, 2945, 2877092729, 2885080595, 7987866⟩,
    ⟨2945, 2959, 2885080595, 2901065811, 7992608⟩,
    ⟨2959, 2973, 2901065811, 2925057795, 7997328⟩,
    ⟨2973, 2987, 2925057795, 2925057795, 8002026⟩,
    ⟨2987, 3001, 2925057795, 2941071199, 8006702⟩,
    ⟨3001, 3016, 2941071199, 2949082887, 8011688⟩,
    ⟨3016, 3031, 2949082887, 2965116185, 8016649⟩,
    ⟨3031, 3046, 2965116185, 2981159357, 8021586⟩,
    ⟨3046, 3061, 2981159357, 2997212353, 8026498⟩,
    ⟨3061, 3076, 2997212353, 3005243740, 8031387⟩,
    ⟨3076, 3091, 3005243740, 3029352493, 8036251⟩,
    ⟨3091, 3106, 3029352493, 3029352493, 8041093⟩,
    ⟨3106, 3121, 3029352493, 3053490223, 8045910⟩,
    ⟨3121, 3136, 3053490223, 3053490223, 8050705⟩,
    ⟨3136, 3151, 3053490223, 3061545700, 8055477⟩,
    ⟨3151, 3166, 3061545700, 3069605926, 8060226⟩,
    ⟨3166, 3181, 3069605926, 3093800782, 8064952⟩,
    ⟨3181, 3196, 3093800782, 3109940096, 8069657⟩,
    ⟨3196, 3211, 3109940096, 3126088774, 8074339⟩,
    ⟨3211, 3227, 3126088774, 3142247394, 8079310⟩,
    ⟨3227, 3243, 3142247394, 3150331650, 8084256⟩,
    ⟨3243, 3259, 3150331650, 3182688358, 8089177⟩,
    ⟨3259, 3275, 3182688358, 3190782433, 8094075⟩,
    ⟨3275, 3291, 3190782433, 3190782433, 8098948⟩,
    ⟨3291, 3307, 3190782433, 3215093827, 8103798⟩,
    ⟨3307, 3323, 3215093827, 3239419702, 8108625⟩,
    ⟨3323, 3339, 3239419702, 3255646558, 8113428⟩,
    ⟨3339, 3355, 3255646558, 3271882976, 8118209⟩,
    ⟨3355, 3371, 3271882976, 3296251874, 8122966⟩,
    ⟨3371, 3387, 3296251874, 3304379575, 8127701⟩,
    ⟨3387, 3403, 3304379575, 3320644403, 8132414⟩,
    ⟨3403, 3420, 3320644403, 3336919197, 8137397⟩,
    ⟨3420, 3437, 3336919197, 3345061553, 8142356⟩,
    ⟨3437, 3454, 3345061553, 3353208843, 8147290⟩,
    ⟨3454, 3471, 3353208843, 3393969843, 8152200⟩,
    ⟨3471, 3488, 3393969843, 3393969843, 8157085⟩,
    ⟨3488, 3505, 3393969843, 3410293737, 8161947⟩,
    ⟨3505, 3522, 3410293737, 3426627309, 8166786⟩,
    ⟨3522, 3539, 3426627309, 3459313713, 8171601⟩,
    ⟨3539, 3556, 3459313713, 3475666499, 8176393⟩,
    ⟨3556, 3573, 3475666499, 3500209985, 8181162⟩,
    ⟨3573, 3590, 3500209985, 3516581803, 8185909⟩,
    ⟨3590, 3607, 3516581803, 3532963069, 8190633⟩,
    ⟨3607, 3625, 3532963069, 3557549902, 8195611⟩,
    ⟨3625, 3643, 3557549902, 3582151594, 8200564⟩,
    ⟨3643, 3661, 3582151594, 3590357087, 8205493⟩,
    ⟨3661, 3679, 3590357087, 3614988281, 8210398⟩,
    ⟨3679, 3697, 3614988281, 3631418837, 8215278⟩,
    ⟨3697, 3715, 3631418837, 3647859107, 8220135⟩,
    ⟨3715, 3733, 3647859107, 3672534014, 8224969⟩,
    ⟨3733, 3751, 3672534014, 3680763793, 8229779⟩,
    ⟨3751, 3769, 3680763793, 3705467491, 8234566⟩,
    ⟨3769, 3787, 3705467491, 3713706822, 8239331⟩,
    ⟨3787, 3805, 3713706822, 3738439041, 8244073⟩,
    ⟨3805, 3824, 3738439041, 3754937149, 8249054⟩,
    ⟨3824, 3843, 3754937149, 3763191159, 8254010⟩,
    ⟨3843, 3862, 3763191159, 3787967985, 8258942⟩,
    ⟨3862, 3881, 3787967985, 3812759535, 8263850⟩,
    ⟨3881, 3900, 3812759535, 3821028268, 8268733⟩,
    ⟨3900, 3919, 3821028268, 3854122640, 8273593⟩,
    ⟨3919, 3938, 3854122640, 3878957930, 8278430⟩,
    ⟨3938, 3957, 3878957930, 3895524416, 8283243⟩,
    ⟨3957, 3976, 3895524416, 3903812449, 8288033⟩,
    ⟨3976, 3995, 3903812449, 3912105249, 8292800⟩,
    ⟨3995, 4014, 3912105249, 3945295429, 8297545⟩,
    ⟨4014, 4034, 3945295429, 3970202974, 8302515⟩,
    ⟨4034, 4054, 3970202974, 3986817896, 8307461⟩,
    ⟨4054, 4074, 3986817896, 4003442660, 8312382⟩,
    ⟨4074, 4094, 4003442660, 4028394497, 8317279⟩,
    ⟨4094, 4096, 4028394497, 4028394497, 8317768⟩
  ]⟩,
  ⟨4096, 8192, [
    ⟨4096, 4116, 4028394497, 4045039775, 8322639⟩,
    ⟨4116, 4136, 4045039775, 4070022233, 8327486⟩,
    ⟨4136, 4156, 4070022233, 4086686853, 8332310⟩,
    ⟨4156, 4176, 4086686853, 4103361075, 8337111⟩,
    ⟨4176, 4196, 4103361075, 4111702963, 8341888⟩,
    ⟨4196, 4216, 4111702963, 4128396251, 8346644⟩,
    ⟨4216, 4237, 4128396251, 4161802699, 8351612⟩,
    ⟨4237, 4258, 4161802699, 4186872367, 8356556⟩,
    ⟨4258, 4279, 4186872367, 4220318271, 8361476⟩,
    ⟨4279, 4300, 4220318271, 4245417387, 8366372⟩,
    ⟨4300, 4321, 4245417387, 4245417387, 8371244⟩,
    ⟨4321, 4342, 4245417387, 4270545663, 8376092⟩,
    ⟨4342, 4363, 4270545663, 4295688414, 8380917⟩,
    ⟨4363, 4384, 4295688414, 4304074132, 8385718⟩,
    ⟨4384, 4405, 4304074132, 4320855126, 8390497⟩,
    ⟨4405, 4427, 4320855126, 4346041563, 8395479⟩,
    ⟨4427, 4449, 4346041563, 4362842435, 8400436⟩,
    ⟨4449, 4471, 4362842435, 4388058542, 8405369⟩,
    ⟨4471, 4493, 4388058542, 4413289373, 8410277⟩,
    ⟨4493, 4515, 4413289373, 4430119697, 8415162⟩,
    ⟨4515, 4537, 4430119697, 4455379766, 8420023⟩,
    ⟨4537, 4559, 4455379766, 4472229486, 8424860⟩,
    ⟨4559, 4581, 4472229486, 4489088834, 8429674⟩,
    ⟨4581, 4603, 4489088834, 4522826694, 8434465⟩,
    ⟨4603, 4626, 4522826694, 4531266143, 8439449⟩,
    ⟨4626, 4649, 4531266143, 4565043779, 8444409⟩,
    ⟨4649, 4672, 4565043779, 4590391811, 8449344⟩,
    ⟨4672, 4695, 4590391811, 4615754576, 8454255⟩,
    ⟨4695, 4718, 4615754576, 4624213718, 8459142⟩,
    ⟨4718, 4741, 4624213718, 4658069738, 8464005⟩,
    ⟨4741, 4764, 4658069738, 4675007426, 8468844⟩,
    ⟨4764, 4787, 4675007426, 4691954748, 8473661⟩,
    ⟨4787, 4810, 4691954748, 4725868564, 8478454⟩,
    ⟨4810, 4834, 4725868564, 4751318857, 8483431⟩,
    ⟨4834, 4858, 4751318857, 4751318857, 8488384⟩,
    ⟨4858, 4882, 4751318857, 4776798793, 8493312⟩,
    ⟨4882, 4906, 4776798793, 4793795225, 8498216⟩,
    ⟨4906, 4930, 4793795225, 4810801417, 8503096⟩,
    ⟨4930, 4954, 4810801417, 4853341177, 8507952⟩,
    ⟨4954, 4978, 4853341177, 4887392317, 8512785⟩,
    ⟨4978, 5002, 4887392317, 4912945102, 8517595⟩,
    ⟨5002, 5027, 4912945102, 4955558002, 8522580⟩,
    ⟨5027, 5052, 4955558002, 4972613084, 8527541⟩,
    ⟨5052, 5077, 4972613084, 4989678038, 8532477⟩,
    ⟨5077, 5102, 4989678038, 5023827594, 8537389⟩,
    ⟨5102, 5127, 5023827594, 5049454425, 8542277⟩,
    ⟨5127, 5152, 5049454425, 5058001567, 8547142⟩,
    ⟨5152, 5177, 5058001567, 5083657516, 8551983⟩,
    ⟨5177, 5202, 5083657516, 5109327916, 8556800⟩,
    ⟨5202, 5228, 5109327916, 5126451488, 8561786⟩,
    ⟨5228, 5254, 5126451488, 5152151726, 8566746⟩,
    ⟨5254, 5280, 5152151726, 5177866775, 8571683⟩,
    ⟨5280, 5306, 5177866775, 5203596560, 8576595⟩,
    ⟨5306, 5332, 5203596560, 5220759526, 8581483⟩,
    ⟨5332, 5358, 5220759526, 5246518570, 8586348⟩,
    ⟨5358, 5384, 5246518570, 5255109758, 8591188⟩,
    ⟨5384, 5410, 5255109758, 5289493782, 8596006⟩,
    ⟨5410, 5437, 5289493782, 5332498702, 8600984⟩,
    ⟨5437, 5464, 5332498702, 5358316516, 8605938⟩,
    ⟨5464, 5491, 5358316516, 5392759984, 8610867⟩,
    ⟨5491, 5518, 5392759984, 5418607300, 8615772⟩,
    ⟨5518, 5545, 5418607300, 5453089912, 8620653⟩,
    ⟨5545, 5572, 5453089912, 5478966445, 8625511⟩,
    ⟨5572, 5599, 5478966445, 5504857480, 8630345⟩,
    ⟨5599, 5626, 5504857480, 5513492635, 8635155⟩,
    ⟨5626, 5654, 5513492635, 5556693235, 8640120⟩,
    ⟨5654, 5682, 5556693235, 5582628415, 8645060⟩,
    ⟨5682, 5710, 5582628415, 5617228319, 8649976⟩,
    ⟨5710, 5738, 5617228319, 5643192920, 8654867⟩,
    ⟨5738, 5766, 5643192920, 5669172125, 8659735⟩,
    ⟨5766, 5794, 5669172125, 5695165865, 8664580⟩,
    ⟨5794, 5822, 5695165865, 5729843469, 8669401⟩,
    ⟨5822, 5851, 5729843469, 5773215314, 8674369⟩,
    ⟨5851, 5880, 5773215314, 5816611884, 8679314⟩,
    ⟨5880, 5909, 5816611884, 5842664583, 8684233⟩,
    ⟨5909, 5938, 5842664583, 5860042841, 8689129⟩,
    ⟨5938, 5967, 5860042841, 5877430843, 8694001⟩,
    ⟨5967, 5996, 5877430843, 5894828541, 8698849⟩,
    ⟨5996, 6025, 5894828541, 5912235889, 8703674⟩,
    ⟨6025, 6055, 5912235889, 5955779094, 8708641⟩,
    ⟨6055, 6085, 5955779094, 5981919846, 8713584⟩,
    ⟨6085, 6115, 5981919846, 6016793854, 8718502⟩,
    ⟨6115, 6145, 6016793854, 6051687438, 8723396⟩,
    ⟨6145, 6175, 6051687438, 6077872236, 8728266⟩,
    ⟨6175, 6205, 6077872236, 6104071572, 8733112⟩,
    ⟨6205, 6236, 6104071572, 6139023956, 8738096⟩,
    ⟨6236, 6267, 6139023956, 6165253121, 8743055⟩,
    ⟨6267, 6298, 6165253121, 6200245077, 8747989⟩,
    ⟨6298, 6329, 6200245077, 6252762471, 8752899⟩,
    ⟨6329, 6360, 6252762471, 6287793611, 8757785⟩,
    ⟨6360, 6391, 6287793611, 6331606851, 8762648⟩,
    ⟨6391, 6422, 6331606851, 6349141823, 8767486⟩,
    ⟨6422, 6454, 6349141823, 6375459194, 8772457⟩,
    ⟨6454, 6486, 6375459194, 6401791403, 8777403⟩,
    ⟨6486, 6518, 6401791403, 6410573727, 8782324⟩,
    ⟨6518, 6550, 6410573727, 6436935393, 8787222⟩,
    ⟨6550, 6582, 6436935393, 6498480058, 8792095⟩,
    ⟨6582, 6614, 6498480058, 6516073948, 8796945⟩,
    ⟨6614, 6647, 6516073948, 6533677792, 8801922⟩,
    ⟨6647, 6680, 6533677792, 6577712167, 8806875⟩,
    ⟨6680, 6713, 6577712167, 6621771182, 8811803⟩,
    ⟨6713, 6746, 6621771182, 6648221303, 8816707⟩,
    ⟨6746, 6779, 6648221303, 6674686061, 8821586⟩,
    ⟨6779, 6812, 6674686061, 6709991833, 8826443⟩,
    ⟨6812, 6846, 6709991833, 6754148938, 8831421⟩,
    ⟨6846, 6880, 6754148938, 6789494438, 8836375⟩,
    ⟨6880, 6914, 6789494438, 6824859658, 8841305⟩,
    ⟨6914, 6948, 6824859658, 6842552080, 8846211⟩,
    ⟨6948, 6982, 6842552080, 6895658632, 8851092⟩,
    ⟨6982, 7016, 6895658632, 6939938382, 8855950⟩,
    ⟨7016, 7051, 6939938382, 6975382086, 8860926⟩,
    ⟨7051, 7086, 6975382086, 7001979720, 8865878⟩,
    ⟨7086, 7121, 7001979720, 7028592135, 8870805⟩,
    ⟨7121, 7156, 7028592135, 7055219259, 8875708⟩,
    ⟨7156, 7191, 7055219259, 7081861020, 8880587⟩,
    ⟨7191, 7226, 7081861020, 7126288230, 8885442⟩,
    ⟨7226, 7262, 7126288230, 7170740290, 8890412⟩,
    ⟨7262, 7298, 7170740290, 7188531004, 8895357⟩,
    ⟨7298, 7334, 7188531004, 7233032394, 8900278⟩,
    ⟨7334, 7370, 7233032394, 7259747916, 8905174⟩,
    ⟨7370, 7406, 7259747916, 7268657963, 8910047⟩,
    ⟨7406, 7443, 7268657963, 7295403056, 8915031⟩,
    ⟨7443, 7480, 7295403056, 7331083016, 8919990⟩,
    ⟨7480, 7517, 7331083016, 7384632560, 8924924⟩,
    ⟨7517, 7554, 7384632560, 7438211564, 8929834⟩,
    ⟨7554, 7591, 7438211564, 7500754604, 8934720⟩,
    ⟨7591, 7628, 7500754604, 7527573350, 8939582⟩,
    ⟨7628, 7666, 7527573350, 7554407006, 8944552⟩,
    ⟨7666, 7704, 7554407006, 7617053478, 8949496⟩,
    ⟨7704, 7742, 7617053478, 7652871146, 8954417⟩,
    ⟨7742, 7780, 7652871146, 7679749085, 8959313⟩,
    ⟨7780, 7818, 7679749085, 7706641643, 8964186⟩,
    ⟨7818, 7857, 7706641643, 7742518291, 8969162⟩,
    ⟨7857, 7896, 7742518291, 7787388856, 8974113⟩,
    ⟨7896, 7935, 7787388856, 7832284056, 8979040⟩,
    ⟨7935, 7974, 7832284056, 7868219828, 8983943⟩,
    ⟨7974, 8013, 7868219828, 7895186294, 8988822⟩,
    ⟨8013, 8053, 7895186294, 7922167697, 8993801⟩,
    ⟨8053, 8093, 7922167697, 7976160233, 8998756⟩,
    ⟨8093, 8133, 7976160233, 8012174981, 9003687⟩,
    ⟨8133, 8173, 8012174981, 8048209353, 9008593⟩,
    ⟨8173, 8192, 8048209353, 8066231183, 9010915⟩
  ]⟩,
  ⟨8192, 16384, [
    ⟨8192, 8232, 8066231183, 8102294327, 9015786⟩,
    ⟨8232, 8273, 8102294327, 8156418851, 9020754⟩,
    ⟨8273, 8314, 8156418851, 8201547341, 9025698⟩,
    ⟨8314, 8355, 8201547341, 8228639192, 9030617⟩,
    ⟨8355, 8396, 8228639192, 8273816752, 9035512⟩,
    ⟨8396, 8437, 8273816752, 8309978288, 9040384⟩,
    ⟨8437, 8479, 8309978288, 8346159684, 9045349⟩,
    ⟨8479, 8521, 8346159684, 8373310554, 9050290⟩,
    ⟨8521, 8563, 8373310554, 8418586589, 9055207⟩,
    ⟨8563, 8605, 8418586589, 8454826989, 9060100⟩,
    ⟨8605, 8648, 8454826989, 8509217499, 9065085⟩,
    ⟨8648, 8691, 8509217499, 8554567724, 9070045⟩,
    ⟨8691, 8734, 8554567724, 8609017604, 9074980⟩,
    ⟨8734, 8777, 8609017604, 8654417059, 9079891⟩,
    ⟨8777, 8820, 8654417059, 8699840954, 9084779⟩,
    ⟨8820, 8864, 8699840954, 8763469239, 9089755⟩,
    ⟨8864, 8908, 8763469239, 8790753360, 9094707⟩,
    ⟨8908, 8952, 8790753360, 8836251530, 9099634⟩,
    ⟨8952, 8996, 8836251530, 8863565141, 9104537⟩,
    ⟨8996, 9040, 8863565141, 8918221637, 9109416⟩,
    ⟨9040, 9085, 8918221637, 8963793542, 9114381⟩,
    ⟨9085, 9130, 8963793542, 9000270830, 9119322⟩,
    ⟨9130, 9175, 9000270830, 9055016264, 9124239⟩,
    ⟨9175, 9220, 9055016264, 9100661924, 9129132⟩,
    ⟨9220, 9266, 9100661924, 9146332469, 9134109⟩,
    ⟨9266, 9312, 9146332469, 9192027774, 9139061⟩,
    ⟨9312, 9358, 9192027774, 9246891702, 9143988⟩,
    ⟨9358, 9404, 9246891702, 9292636162, 9148892⟩,
    ⟨9404, 9451, 9292636162, 9356713301, 9153877⟩,
    ⟨9451, 9498, 9356713301, 9420825167, 9158838⟩,
    ⟨9498, 9545, 9420825167, 9457480263, 9163774⟩,
    ⟨9545, 9592, 9457480263, 9484986321, 9168686⟩,
    ⟨9592, 9639, 9484986321, 9540027765, 9173574⟩,
    ⟨9639, 9687, 9540027765, 9585920475, 9178542⟩,
    ⟨9687, 9735, 9585920475, 9631837895, 9183484⟩,
    ⟨9735, 9783, 9631837895, 9686968313, 9188403⟩,
    ⟨9783, 9831, 9686968313, 9742128095, 9193297⟩,
    ⟨9831, 9880, 9742128095, 9797317709, 9198269⟩,
    ⟨9880, 9929, 9797317709, 9852537011, 9203217⟩,
    ⟨9929, 9978, 9852537011, 9898577706, 9208139⟩,
    ⟨9978, 10027, 9898577706, 9917003782, 9213038⟩,
    ⟨10027, 10077, 9917003782, 9963093842, 9218012⟩,
    ⟨10077, 10127, 9963093842, 10018431614, 9222962⟩,
    ⟨10127, 10177, 10018431614, 10092254710, 9227887⟩,
    ⟨10177, 10227, 10092254710, 10129185862, 9232788⟩,
    ⟨10227, 10278, 10129185862, 10193850196, 9237762⟩,
    ⟨10278, 10329, 10193850196, 10240063756, 9242712⟩,
    ⟨10329, 10380, 10240063756, 10295549584, 9247638⟩,
    ⟨10380, 10431, 10295549584, 10332559740, 9252539⟩,
    ⟨10431, 10483, 10332559740, 10388104812, 9257512⟩,
    ⟨10483, 10535, 10388104812, 10443679572, 9262460⟩,
    ⟨10535, 10587, 10443679572, 10462214340, 9267384⟩,
    ⟨10587, 10639, 10462214340, 10536392604, 9272283⟩,
    ⟨10639, 10692, 10536392604, 10592056122, 9277253⟩,
    ⟨10692, 10745, 10592056122, 10647749304, 9282197⟩,
    ⟨10745, 10798, 10647749304, 10684897776, 9287118⟩,
    ⟨10798, 10851, 10684897776, 10722065832, 9292014⟩,
    ⟨10851, 10905, 10722065832, 10796441656, 9296978⟩,
    ⟨10905, 10959, 10796441656, 10842951246, 9301918⟩,
    ⟨10959, 11013, 10842951246, 10889485411, 9306833⟩,
    ⟨11013, 11068, 10889485411, 10926732671, 9311815⟩,
    ⟨11068, 11123, 10926732671, 11001266847, 9316772⟩,
    ⟨11123, 11178, 11001266847, 11066518775, 9321704⟩,
    ⟨11178, 11233, 11066518775, 11085172001, 9326613⟩,
    ⟨11233, 11289, 11085172001, 11159824689, 9331586⟩,
    ⟨11289, 11345, 11159824689, 11206507359, 9336534⟩,
    ⟨11345, 11401, 11206507359, 11262556107, 9341458⟩,
    ⟨11401, 11458, 11262556107, 11309288332, 9346445⟩,
    ⟨11458, 11515, 11309288332, 11374748181, 9351407⟩,
    ⟨11515, 11572, 11374748181, 11412173561, 9356345⟩,
    ⟨11572, 11629, 11412173561, 11468341115, 9361259⟩,
    ⟨11629, 11687, 11468341115, 11505806051, 9366234⟩,
    ⟨11687, 11745, 11505806051, 11571404339, 9371184⟩,
    ⟨11745, 11803, 11571404339, 11618284894, 9376111⟩,
    ⟨11803, 11862, 11618284894, 11683952573, 9381097⟩,
    ⟨11862, 11921, 11683952573, 11740268921, 9386058⟩,
    ⟨11921, 11980, 11740268921, 11824787876, 9390995⟩,
    ⟨11980, 12039, 11824787876, 11871767416, 9395908⟩,
    ⟨12039, 12099, 11871767416, 11928172696, 9400880⟩,
    ⟨12099, 12159, 11928172696, 12003419304, 9405826⟩,
    ⟨12159, 12219, 12003419304, 12050473049, 9410749⟩,
    ⟨12219, 12280, 12050473049, 12125798881, 9415729⟩,
    ⟨12280, 12341, 12125798881, 12172902301, 9420684⟩,
    ⟨12341, 12402, 12172902301, 12238881606, 9425615⟩,
    ⟨12402, 12464, 12238881606, 12304895813, 9430601⟩,
    ⟨12464, 12526, 12304895813, 12380380317, 9435563⟩,
    ⟨12526, 12588, 12380380317, 12455904325, 9440501⟩,
    ⟨12588, 12650, 12455904325, 12531467637, 9445414⟩,
    ⟨12650, 12713, 12531467637, 12597620311, 9450382⟩,
    ⟨12713, 12776, 12597620311, 12644896936, 9455325⟩,
    ⟨12776, 12839, 12644896936, 12711118644, 9460244⟩,
    ⟨12839, 12903, 12711118644, 12758444729, 9465217⟩,
    ⟨12903, 12967, 12758444729, 12843676205, 9470164⟩,
    ⟨12967, 13031, 12843676205, 12910001821, 9475088⟩,
    ⟨13031, 13096, 12910001821, 12966882205, 9480064⟩,
    ⟨13096, 13161, 12966882205, 13042762325, 9485015⟩,
    ⟨13161, 13226, 13042762325, 13109191912, 9489941⟩,
    ⟨13226, 13292, 13109191912, 13166161426, 9494919⟩,
    ⟨13292, 13358, 13166161426, 13232660530, 9499872⟩,
    ⟨13358, 13424, 13232660530, 13299194137, 9504801⟩,
    ⟨13424, 13491, 13299194137, 13365762597, 9509780⟩,
    ⟨13491, 13558, 13365762597, 13413336267, 9514734⟩,
    ⟨13558, 13625, 13413336267, 13470454245, 9519663⟩,
    ⟨13625, 13693, 13470454245, 13556176023, 9524642⟩,
    ⟨13693, 13761, 13556176023, 13641942378, 9529595⟩,
    ⟨13761, 13829, 13641942378, 13699149528, 9534525⟩,
    ⟨13829, 13898, 13699149528, 13765926042, 9539502⟩,
    ⟨13898, 13967, 13765926042, 13851826128, 9544454⟩,
    ⟨13967, 14036, 13851826128, 13909122420, 9549382⟩,
    ⟨14036, 14106, 13909122420, 13966448562, 9554357⟩,
    ⟨14106, 14176, 13966448562, 14023804404, 9559307⟩,
    ⟨14176, 14246, 14023804404, 14071625569, 9564233⟩,
    ⟨14246, 14317, 14071625569, 14119471589, 9569204⟩,
    ⟨14317, 14388, 14119471589, 14186490646, 9574151⟩,
    ⟨14388, 14459, 14186490646, 14282281386, 9579074⟩,
    ⟨14459, 14531, 14282281386, 14330201591, 9584041⟩,
    ⟨14531, 14603, 14330201591, 14426091431, 9588984⟩,
    ⟨14603, 14676, 14426091431, 14502843191, 9593970⟩,
    ⟨14676, 14749, 14502843191, 14589233579, 9598932⟩,
    ⟨14749, 14822, 14589233579, 14675668400, 9603869⟩,
    ⟨14822, 14896, 14675668400, 14762148041, 9608849⟩,
    ⟨14896, 14970, 14762148041, 14839058481, 9613805⟩,
    ⟨14970, 15044, 14839058481, 14877533425, 9618736⟩,
    ⟨15044, 15119, 14877533425, 14954523097, 9623709⟩,
    ⟨15119, 15194, 14954523097, 15041181010, 9628657⟩,
    ⟨15194, 15269, 15041181010, 15118249658, 9633581⟩,
    ⟨15269, 15345, 15118249658, 15214635118, 9638546⟩,
    ⟨15345, 15421, 15214635118, 15301426501, 9643487⟩,
    ⟨15421, 15498, 15301426501, 15388262713, 9648468⟩,
    ⟨15498, 15575, 15388262713, 15446183257, 9653424⟩,
    ⟨15575, 15652, 15446183257, 15542766807, 9658355⟩,
    ⟨15652, 15730, 15542766807, 15600746763, 9663326⟩,
    ⟨15730, 15808, 15600746763, 15716766039, 9668273⟩,
    ⟨15808, 15887, 15716766039, 15784478845, 9673258⟩,
    ⟨15887, 15966, 15784478845, 15861904589, 9678218⟩,
    ⟨15966, 16045, 15861904589, 15920003513, 9683154⟩,
    ⟨16045, 16125, 15920003513, 16026572921, 9688128⟩,
    ⟨16125, 16205, 16026572921, 16094424460, 9693077⟩,
    ⟨16205, 16286, 16094424460, 16172008964, 9698063⟩,
    ⟨16286, 16367, 16172008964, 16239930132, 9703024⟩,
    ⟨16367, 16384, 16239930132, 16259338256, 9704062⟩
  ]⟩,
  ⟨16384, 32768, [
    ⟨16384, 16465, 16259338256, 16337010208, 9708994⟩,
    ⟨16465, 16547, 16337010208, 16405007942, 9713962⟩,
    ⟨16547, 16629, 16405007942, 16473040277, 9718905⟩,
    ⟨16629, 16712, 16473040277, 16580003001, 9723884⟩,
    ⟨16712, 16795, 16580003001, 16638376029, 9728838⟩,
    ⟨16795, 16878, 16638376029, 16696778637, 9733768⟩,
    ⟨16878, 16962, 16696778637, 16794165957, 9738732⟩,
    ⟨16962, 17046, 16794165957, 16901346349, 9743672⟩,
    ⟨17046, 17131, 16901346349, 16979335517, 9748646⟩,
    ⟨17131, 17216, 16979335517, 17067117881, 9753596⟩,
    ⟨17216, 17302, 17067117881, 17125669355, 9758579⟩,
    ⟨17302, 17388, 17125669355, 17223304725, 9763537⟩,
    ⟨17388, 17474, 17223304725, 17320989435, 9768471⟩,
    ⟨17474, 17561, 17320989435, 17408950368, 9773437⟩,
    ⟨17561, 17648, 17408950368, 17496955779, 9778379⟩,
    ⟨17648, 17736, 17496955779, 17575222603, 9783353⟩,
    ⟨17736, 17824, 17575222603, 17653529027, 9788303⟩,
    ⟨17824, 17913, 17653529027, 17751461857, 9793283⟩,
    ⟨17913, 18002, 17751461857, 17859242497, 9798240⟩,
    ⟨18002, 18092, 17859242497, 17947471540, 9803227⟩,
    ⟨18092, 18182, 17947471540, 18045553430, 9808189⟩,
    ⟨18182, 18272, 18045553430, 18153497827, 9813127⟩,
    ⟨18272, 18363, 18153497827, 18241860682, 9818095⟩,
    ⟨18363, 18454, 18241860682, 18349914100, 9823038⟩,
    ⟨18454, 18546, 18349914100, 18448194210, 9828011⟩,
    ⟨18546, 18638, 18448194210, 18507191964, 9832959⟩,
    ⟨18638, 18731, 18507191964, 18585895460, 9837937⟩,
    ⟨18731, 18824, 18585895460, 18664638572, 9842889⟩,
    ⟨18824, 18918, 18664638572, 18733573669, 9847871⟩,
    ⟨18918, 19012, 18733573669, 18802543458, 9852827⟩,
    ⟨19012, 19107, 18802543458, 18891263766, 9857812⟩,
    ⟨19107, 19202, 18891263766, 18960303163, 9862771⟩,
    ⟨19202, 19298, 18960303163, 19068848501, 9867758⟩,
    ⟨19298, 19394, 19068848501, 19157702990, 9872721⟩,
    ⟨19394, 19490, 19157702990, 19315745518, 9877658⟩,
    ⟨19490, 19587, 19315745518, 19414571748, 9882623⟩,
    ⟨19587, 19684, 19414571748, 19464009563, 9887563⟩,
    ⟨19684, 19782, 19464009563, 19582719911, 9892529⟩,
    ⟨19782, 19880, 19582719911, 19671797150, 9897471⟩,
    ⟨19880, 19979, 19671797150, 19780723979, 9902439⟩,
    ⟨19979, 20078, 19780723979, 19889705170, 9907381⟩,
    ⟨20078, 20178, 19889705170, 20018565720, 9912350⟩,
    ⟨20178, 20278, 20018565720, 20097904064, 9917293⟩,
    ⟨20278, 20379, 20097904064, 20207048946, 9922262⟩,
    ⟨20379, 20480, 20207048946, 20306321006, 9927206⟩,
    ⟨20480, 20582, 20306321006, 20395710572, 9932174⟩,
    ⟨20582, 20684, 20395710572, 20475207508, 9937117⟩,
    ⟨20684, 20787, 20475207508, 20594512528, 9942085⟩,
    ⟨20787, 20890, 20594512528, 20674088744, 9947027⟩,
    ⟨20890, 20994, 20674088744, 20783560667, 9951993⟩,
    ⟨20994, 21098, 20783560667, 20893086952, 9956935⟩,
    ⟨21098, 21203, 20893086952, 21022591639, 9961899⟩,
    ⟨21203, 21309, 21022591639, 21092359841, 9966886⟩,
    ⟨21309, 21415, 21092359841, 21221993865, 9971848⟩,
    ⟨21415, 21522, 21221993865, 21331739017, 9976832⟩,
    ⟨21522, 21629, 21331739017, 21471484105, 9981792⟩,
    ⟨21629, 21737, 21471484105, 21561365062, 9986773⟩,
    ⟨21737, 21845, 21561365062, 21681265810, 9991729⟩,
    ⟨21845, 21954, 21681265810, 21781232870, 9996706⟩,
    ⟨21954, 22063, 21781232870, 21901252778, 10001659⟩,
    ⟨22063, 22173, 21901252778, 22051352258, 10006632⟩,
    ⟨22173, 22283, 22051352258, 22151468068, 10011581⟩,
    ⟨22283, 22394, 22151468068, 22241617018, 10016550⟩,
    ⟨22394, 22505, 22241617018, 22341831958, 10021494⟩,
    ⟨22505, 22617, 22341831958, 22432070089, 10026459⟩,
    ⟨22617, 22730, 22432070089, 22582541719, 10031442⟩,
    ⟨22730, 22843, 22582541719, 22682905739, 10036402⟩,
    ⟨22843, 22957, 22682905739, 22783319539, 10041380⟩,
    ⟨22957, 23071, 22783319539, 22954107200, 10046333⟩,
    ⟨23071, 23186, 22954107200, 23044568945, 10051305⟩,
    ⟨23186, 23301, 23044568945, 23165243981, 10056253⟩,
    ⟨23301, 23417, 23165243981, 23265856171, 10061219⟩,
    ⟨23417, 23534, 23265856171, 23336319592, 10066203⟩,
    ⟨23534, 23651, 23336319592, 23497458184, 10071162⟩,
    ⟨23651, 23769, 23497458184, 23628447991, 10076139⟩,
    ⟨23769, 23887, 23628447991, 23759502174, 10081091⟩,
    ⟨23887, 24006, 23759502174, 23880534906, 10086061⟩,
    ⟨24006, 24126, 23880534906, 24052082705, 10091047⟩,
    ⟨24126, 24246, 24052082705, 24163138793, 10096008⟩,
    ⟨24246, 24367, 24163138793, 24233845702, 10100987⟩,
    ⟨24367, 24488, 24233845702, 24365222922, 10105940⟩,
    ⟨24488, 24610, 24365222922, 24456221112, 10110910⟩,
    ⟨24610, 24733, 24456221112, 24567495957, 10115895⟩,
    ⟨24733, 24856, 24567495957, 24678825373, 10120856⟩,
    ⟨24856, 24980, 24678825373, 24810461189, 10125832⟩,
    ⟨24980, 25104, 24810461189, 24901638245, 10130784⟩,
    ⟨25104, 25229, 24901638245, 25033403008, 10135751⟩,
    ⟨25229, 25355, 25033403008, 25165232537, 10140733⟩,
    ⟨25355, 25481, 25165232537, 25307272197, 10145690⟩,
    ⟨25481, 25608, 25307272197, 25408778817, 10150662⟩,
    ⟨25608, 25736, 25408778817, 25540802241, 10155648⟩,
    ⟨25736, 25864, 25540802241, 25662729549, 10160609⟩,
    ⟨25864, 25993, 25662729549, 25794882141, 10165584⟩,
    ⟨25993, 26122, 25794882141, 25937269631, 10170535⟩,
    ⟨26122, 26252, 25937269631, 26069551118, 10175499⟩,
    ⟨26252, 26383, 26069551118, 26191716842, 10180477⟩,
    ⟨26383, 26514, 26191716842, 26344498292, 10185430⟩,
    ⟨26514, 26646, 26344498292, 26436211856, 10190396⟩,
    ⟨26646, 26779, 26436211856, 26609533231, 10195375⟩,
    ⟨26779, 26912, 26609533231, 26752337837, 10200329⟩,
    ⟨26912, 27046, 26752337837, 26885006685, 10205296⟩,
    ⟨27046, 27181, 26885006685, 27007529985, 10210275⟩,
    ⟨27181, 27316, 27007529985, 27130112733, 10215229⟩,
    ⟨27316, 27452, 27130112733, 27242534889, 10220196⟩,
    ⟨27452, 27589, 27242534889, 27365236977, 10225174⟩,
    ⟨27589, 27726, 27365236977, 27467538247, 10230127⟩,
    ⟨27726, 27864, 27467538247, 27672240087, 10235092⟩,
    ⟨27864, 28003, 27672240087, 27815601039, 10240068⟩,
    ⟨28003, 28143, 27815601039, 27948786754, 10245055⟩,
    ⟨28143, 28283, 27948786754, 28061536952, 10250018⟩,
    ⟨28283, 28424, 28061536952, 28184596844, 10254991⟩,
    ⟨28424, 28566, 28184596844, 28338496454, 10259974⟩,
    ⟨28566, 28708, 28338496454, 28543795114, 10264933⟩,
    ⟨28708, 28851, 28543795114, 28687573728, 10269901⟩,
    ⟨28851, 28995, 28687573728, 28810872288, 10274880⟩,
    ⟨28995, 29139, 28810872288, 28954789964, 10279834⟩,
    ⟨29139, 29284, 28954789964, 29098777136, 10284798⟩,
    ⟨29284, 29430, 29098777136, 29273703243, 10289771⟩,
    ⟨29430, 29577, 29273703243, 29397240291, 10294754⟩,
    ⟨29577, 29724, 29397240291, 29531136547, 10299712⟩,
    ⟨29724, 29872, 29531136547, 29654792683, 10304678⟩,
    ⟨29872, 30021, 29654792683, 29778508531, 10309654⟩,
    ⟨30021, 30171, 29778508531, 29943542739, 10314638⟩,
    ⟨30171, 30321, 29943542739, 30098336694, 10319597⟩,
    ⟨30321, 30472, 30098336694, 30222231474, 10324565⟩,
    ⟨30472, 30624, 30222231474, 30346185966, 10329541⟩,
    ⟨30624, 30777, 30346185966, 30511538350, 10334524⟩,
    ⟨30777, 30930, 30511538350, 30666630595, 10339483⟩,
    ⟨30930, 31084, 30666630595, 30832141795, 10344450⟩,
    ⟨31084, 31239, 30832141795, 31008082003, 10349424⟩,
    ⟨31239, 31395, 31008082003, 31194461293, 10354405⟩,
    ⟨31395, 31551, 31194461293, 31318773637, 10359362⟩,
    ⟨31551, 31708, 31318773637, 31453509875, 10364326⟩,
    ⟨31708, 31866, 31453509875, 31598680019, 10369296⟩,
    ⟨31866, 32025, 31598680019, 31712797033, 10374274⟩,
    ⟨32025, 32185, 31712797033, 31899623659, 10379257⟩,
    ⟨32185, 32345, 31899623659, 32076155331, 10384216⟩,
    ⟨32345, 32506, 32076155331, 32273549770, 10389181⟩,
    ⟨32506, 32668, 32273549770, 32450250371, 10394153⟩,
    ⟨32668, 32768, 32450250371, 32523030834, 10397209⟩
  ]⟩,
  ⟨32768, 65536, [
    ⟨32768, 32931, 32523030834, 32689465570, 10402171⟩,
    ⟨32931, 33095, 32689465570, 32897608350, 10407139⟩,
    ⟨33095, 33260, 32897608350, 33043377918, 10412112⟩,
    ⟨33260, 33426, 33043377918, 33220468465, 10417091⟩,
    ⟨33426, 33593, 33220468465, 33408065797, 10422074⟩,
    ⟨33593, 33760, 33408065797, 33595752391, 10427033⟩,
    ⟨33760, 33928, 33595752391, 33773096340, 10431997⟩,
    ⟨33928, 34097, 33773096340, 33898339932, 10436966⟩,
    ⟨34097, 34267, 33898339932, 34075852912, 10441940⟩,
    ⟨34267, 34438, 34075852912, 34253450501, 10446917⟩,
    ⟨34438, 34610, 34253450501, 34452036582, 10451899⟩,
    ⟨34610, 34783, 34452036582, 34640260530, 10456886⟩,
    ⟨34783, 34956, 34640260530, 34786726388, 10461847⟩,
    ⟨34956, 35130, 34786726388, 34964662192, 10466812⟩,
    ⟨35130, 35305, 34964662192, 35111267126, 10471781⟩,
    ⟨35305, 35481, 35111267126, 35289371944, 10476754⟩,
    ⟨35481, 35658, 35289371944, 35457079624, 10481730⟩,
    ⟨35658, 35836, 35457079624, 35593406854, 10486710⟩,
    ⟨35836, 36015, 35593406854, 35813732386, 10491692⟩,
    ⟨36015, 36195, 35813732386, 35971182556, 10496678⟩,
    ⟨36195, 36375, 35971182556, 36149710419, 10501639⟩,
    ⟨36375, 36556, 36149710419, 36317816051, 10506602⟩,
    ⟨36556, 36738, 36317816051, 36517535843, 10511568⟩,
    ⟨36738, 36921, 36517535843, 36738383120, 10516537⟩,
    ⟨36921, 37105, 36738383120, 36927770282, 10521509⟩,
    ⟨37105, 37290, 36927770282, 37085667512, 10526482⟩,
    ⟨37290, 37476, 37085667512, 37264702298, 10531458⟩,
    ⟨37476, 37663, 37264702298, 37528113173, 10536435⟩,
    ⟨37663, 37851, 37528113173, 37654610141, 10541414⟩,
    ⟨37851, 38040, 37654610141, 37833898856, 10546395⟩,
    ⟨38040, 38230, 37833898856, 37992169511, 10551377⟩,
    ⟨38230, 38421, 37992169511, 38182184009, 10556361⟩,
    ⟨38421, 38613, 38182184009, 38351165545, 10561346⟩,
    ⟨38613, 38806, 38351165545, 38573058517, 10566332⟩,
    ⟨38806, 39000, 38573058517, 38763342241, 10571318⟩,
    ⟨39000, 39195, 38763342241, 38964292055, 10576306⟩,
    ⟨39195, 39390, 38964292055, 39186498704, 10581269⟩,
    ⟨39390, 39586, 39186498704, 39366464648, 10586232⟩,
    ⟨39586, 39783, 39366464648, 39546514980, 10591196⟩,
    ⟨39783, 39981, 39546514980, 39758438200, 10596161⟩,
    ⟨39981, 40180, 39758438200, 39970460720, 10601126⟩,
    ⟨40180, 40380, 39970460720, 40118945994, 10606091⟩,
    ⟨40380, 40581, 40118945994, 40309945020, 10611057⟩,
    ⟨40581, 40783, 40309945020, 40479801372, 10616022⟩,
    ⟨40783, 40986, 40479801372, 40702842099, 10620987⟩,
    ⟨40986, 41190, 40702842099, 40925987091, 10625952⟩,
    ⟨41190, 41395, 40925987091, 41138605431, 10630917⟩,
    ⟨41395, 41601, 41138605431, 41330051289, 10635881⟩,
    ⟨41601, 41809, 41330051289, 41564150385, 10640868⟩,
    ⟨41809, 42018, 41564150385, 41809005050, 10645855⟩,
    ⟨42018, 42228, 41809005050, 42043323530, 10650840⟩,
    ⟨42228, 42439, 42043323530, 42267095855, 10655825⟩,
    ⟨42439, 42651, 42267095855, 42490972802, 10660807⟩,
    ⟨42651, 42864, 42490972802, 42757617527, 10665789⟩,
    ⟨42864, 43078, 42757617527, 42960362138, 10670769⟩,
    ⟨43078, 43293, 42960362138, 43131174106, 10675748⟩,
    ⟨43293, 43509, 43131174106, 43302065706, 10680725⟩,
    ⟨43509, 43726, 43302065706, 43526465406, 10685700⟩,
    ⟨43726, 43944, 43526465406, 43697516174, 10690673⟩,
    ⟨43944, 44163, 43697516174, 43964907274, 10695644⟩,
    ⟨44163, 44383, 43964907274, 44189620147, 10700613⟩,
    ⟨44383, 44604, 44189620147, 44382320587, 10705580⟩,
    ⟨44604, 44827, 44382320587, 44628663628, 10710567⟩,
    ⟨44827, 45051, 44628663628, 44832259116, 10715552⟩,
    ⟨45051, 45276, 44832259116, 45035949262, 10720534⟩,
    ⟨45276, 45502, 45035949262, 45261185035, 10725513⟩,
    ⟨45502, 45729, 45261185035, 45475794815, 10730489⟩,
    ⟨45729, 45957, 45475794815, 45690504075, 10735463⟩,
    ⟨45957, 46186, 45690504075, 45916053189, 10740434⟩,
    ⟨46186, 46416, 45916053189, 46120215808, 10745401⟩,
    ⟨46416, 46648, 46120215808, 46367474709, 10750387⟩,
    ⟨46648, 46881, 46367474709, 46625603565, 10755369⟩,
    ⟨46881, 47115, 46625603565, 46787008785, 10760348⟩,
    ⟨47115, 47350, 46787008785, 47023845913, 10765324⟩,
    ⟨47350, 47586, 47023845913, 47282332993, 10770295⟩,
    ⟨47586, 47823, 47282332993, 47551714568, 10775263⟩,
    ⟨47823, 48062, 47551714568, 47767319548, 10780249⟩,
    ⟨48062, 48302, 47767319548, 47983024148, 10785230⟩,
    ⟨48302, 48543, 47983024148, 48252779323, 10790207⟩,
    ⟨48543, 48785, 48252779323, 48479478103, 10795180⟩,
    ⟨48785, 49028, 48479478103, 48717081359, 10800148⟩,
    ⟨49028, 49273, 48717081359, 48987209684, 10805133⟩,
    ⟨49273, 49519, 48987209684, 49235842283, 10810113⟩,
    ⟨49519, 49766, 49235842283, 49495404419, 10815089⟩,
    ⟨49766, 50014, 49495404419, 49744265799, 10820060⟩,
    ⟨50014, 50264, 49744265799, 50025716995, 10825046⟩,
    ⟨50264, 50515, 50025716995, 50263977589, 10830027⟩,
    ⟨50515, 50767, 50263977589, 50480677649, 10835003⟩,
    ⟨50767, 51020, 50480677649, 50719157077, 10839974⟩,
    ⟨51020, 51275, 50719157077, 50968591157, 10844960⟩,
    ⟨51275, 51531, 50968591157, 51272389477, 10849940⟩,
    ⟨51531, 51788, 51272389477, 51532907437, 10854915⟩,
    ⟨51788, 52046, 51532907437, 51793544677, 10859885⟩,
    ⟨52046, 52306, 51793544677, 52065166377, 10864868⟩,
    ⟨52306, 52567, 52065166377, 52293433122, 10869845⟩,
    ⟨52567, 52829, 52293433122, 52543553913, 10874817⟩,
    ⟨52829, 53093, 52543553913, 52826428765, 10879802⟩,
    ⟨53093, 53358, 52826428765, 53087663509, 10884781⟩,
    ⟨53358, 53624, 53087663509, 53349017605, 10889754⟩,
    ⟨53624, 53892, 53349017605, 53621386080, 10894739⟩,
    ⟨53892, 54161, 53621386080, 53872079594, 10899718⟩,
    ⟨54161, 54431, 53872079594, 54144696869, 10904691⟩,
    ⟨54431, 54703, 54144696869, 54439258094, 10909675⟩,
    ⟨54703, 54976, 54439258094, 54690295136, 10914654⟩,
    ⟨54976, 55250, 54690295136, 54974205386, 10919625⟩,
    ⟨55250, 55526, 54974205386, 55192697546, 10924608⟩,
    ⟨55526, 55803, 55192697546, 55487796314, 10929584⟩,
    ⟨55803, 56082, 55487796314, 55793964330, 10934572⟩,
    ⟨56082, 56362, 55793964330, 56056513578, 10939552⟩,
    ⟨56362, 56643, 56056513578, 56384849328, 10944525⟩,
    ⟨56643, 56926, 56384849328, 56713334598, 10949509⟩,
    ⟨56926, 57210, 56713334598, 57031014663, 10954485⟩,
    ⟨57210, 57496, 57031014663, 57305001463, 10959472⟩,
    ⟨57496, 57783, 57305001463, 57590077189, 10964451⟩,
    ⟨57783, 58071, 57590077189, 57897221033, 10969423⟩,
    ⟨58071, 58361, 57897221033, 58171581158, 10974405⟩,
    ⟨58361, 58652, 58171581158, 58468024364, 10979378⟩,
    ⟨58652, 58945, 58468024364, 58742633414, 10984362⟩,
    ⟨58945, 59239, 58742633414, 59105281535, 10989337⟩,
    ⟨59239, 59535, 59105281535, 59402128202, 10994321⟩,
    ⟨59535, 59832, 59402128202, 59710108518, 10999297⟩,
    ⟨59832, 60131, 59710108518, 59974211286, 11004282⟩,
    ⟨60131, 60431, 59974211286, 60249442761, 11009259⟩,
    ⟨60431, 60733, 60249442761, 60546827349, 11014244⟩,
    ⟨60733, 61036, 60546827349, 60844346316, 11019221⟩,
    ⟨61036, 61341, 60844346316, 61086878826, 11024205⟩,
    ⟨61341, 61647, 61086878826, 61428783437, 11029181⟩,
    ⟨61647, 61955, 61428783437, 61693603397, 11034165⟩,
    ⟨61955, 62264, 61693603397, 62024777597, 11039140⟩,
    ⟨62264, 62575, 62024777597, 62300880672, 11044123⟩,
    ⟨62575, 62887, 62300880672, 62599206264, 11049096⟩,
    ⟨62887, 63201, 62599206264, 62897666343, 11054077⟩,
    ⟨63201, 63517, 62897666343, 63229438263, 11059064⟩,
    ⟨63517, 63834, 63229438263, 63627743811, 11064043⟩,
    ⟨63834, 64153, 63627743811, 63904469511, 11069028⟩,
    ⟨64153, 64473, 63904469511, 64170245583, 11074003⟩,
    ⟨64473, 64795, 64170245583, 64469378178, 11078985⟩,
    ⟨64795, 65118, 64469378178, 64779729002, 11083958⟩,
    ⟨65118, 65443, 64779729002, 65123486018, 11088936⟩,
    ⟨65443, 65536, 65123486018, 65190028154, 11090356⟩
  ]⟩
]

theorem rangeChecked01 : checkGroups rangeGroups01 = true := by decide +kernel

def rangeGroups02 : List Group := [
  ⟨65536, 131072, [
    ⟨65536, 65863, 65190028154, 65600555512, 11095334⟩,
    ⟨65863, 66192, 65600555512, 65922464676, 11100316⟩,
    ⟨66192, 66522, 65922464676, 66177886323, 11105289⟩,
    ⟨66522, 66854, 66177886323, 66522304631, 11110268⟩,
    ⟨66854, 67188, 66522304631, 66877992663, 11115251⟩,
    ⟨67188, 67523, 66877992663, 67244960088, 11120225⟩,
    ⟨67523, 67860, 67244960088, 67600966616, 11125204⟩,
    ⟨67860, 68199, 67600966616, 67912611852, 11130187⟩,
    ⟨68199, 68539, 67912611852, 68235531492, 11135160⟩,
    ⟨68539, 68881, 68235531492, 68547455328, 11140137⟩,
    ⟨68881, 69225, 68547455328, 68881808898, 11145119⟩,
    ⟨69225, 69571, 68881808898, 69216312048, 11150105⟩,
    ⟨69571, 69918, 69216312048, 69495189048, 11155080⟩,
    ⟨69918, 70267, 69495189048, 69885791113, 11160059⟩,
    ⟨70267, 70618, 69885791113, 70231907415, 11165042⟩,
    ⟨70618, 70971, 70231907415, 70600518339, 11170028⟩,
    ⟨70971, 71325, 70600518339, 70946943463, 11175004⟩,
    ⟨71325, 71681, 70946943463, 71349422815, 11179982⟩,
    ⟨71681, 72039, 71349422815, 71740896555, 11184964⟩,
    ⟨72039, 72399, 71740896555, 72121354821, 11189949⟩,
    ⟨72399, 72760, 72121354821, 72468397434, 11194923⟩,
    ⟨72760, 73123, 72468397434, 72849194034, 11199900⟩,
    ⟨73123, 73488, 72849194034, 73162930646, 11204879⟩,
    ⟨73488, 73855, 73162930646, 73521646166, 11209860⟩,
    ⟨73855, 74224, 73521646166, 73914165706, 11214844⟩,
    ⟨74224, 74595, 73914165706, 74284420096, 11219830⟩,
    ⟨74595, 74967, 74284420096, 74688513076, 11224805⟩,
    ⟨74967, 75341, 74688513076, 75025406506, 11229781⟩,
    ⟨75341, 75717, 75025406506, 75441092589, 11234759⟩,
    ⟨75717, 76095, 75441092589, 75789524498, 11239739⟩,
    ⟨76095, 76475, 75789524498, 76138110849, 11244721⟩,
    ⟨76475, 76857, 76138110849, 76520600751, 11249703⟩,
    ⟨76857, 77241, 76520600751, 76869496048, 11254687⟩,
    ⟨77241, 77627, 76869496048, 77342402272, 11259672⟩,
    ⟨77627, 78015, 77342402272, 77725400644, 11264658⟩,
    ⟨78015, 78405, 77725400644, 78086029252, 11269644⟩,
    ⟨78405, 78797, 78086029252, 78469366740, 11274632⟩,
    ⟨78797, 79190, 78469366740, 78830314164, 11279607⟩,
    ⟨79190, 79585, 78830314164, 79213989952, 11284582⟩,
    ⟨79585, 79982, 79213989952, 79654282714, 11289558⟩,
    ⟨79982, 80381, 79654282714, 80060885974, 11294535⟩,
    ⟨80381, 80782, 80060885974, 80467668370, 11299511⟩,
    ⟨80782, 81185, 80467668370, 80919847850, 11304487⟩,
    ⟨81185, 81590, 80919847850, 81304369592, 11309463⟩,
    ⟨81590, 81997, 81304369592, 81723003835, 11314439⟩,
    ⟨81997, 82406, 81723003835, 82164461020, 11319415⟩,
    ⟨82406, 82818, 82164461020, 82606112698, 11324402⟩,
    ⟨82818, 83232, 82606112698, 82957323757, 11329389⟩,
    ⟨83232, 83648, 82957323757, 83388029969, 11334374⟩,
    ⟨83648, 84066, 83388029969, 83750889457, 11339359⟩,
    ⟨84066, 84486, 83750889457, 84204663177, 11344343⟩,
    ⟨84486, 84908, 84204663177, 84579190902, 11349325⟩,
    ⟨84908, 85332, 84579190902, 85010654530, 11354306⟩,
    ⟨85332, 85758, 85010654530, 85442307398, 11359286⟩,
    ⟨85758, 86186, 85442307398, 85828692408, 11364265⟩,
    ⟨86186, 86616, 85828692408, 86306200530, 11369241⟩,
    ⟨86616, 87049, 86306200530, 86692924282, 11374228⟩,
    ⟨87049, 87484, 86692924282, 87102575950, 11379213⟩,
    ⟨87484, 87921, 87102575950, 87614864725, 11384195⟩,
    ⟨87921, 88360, 87614864725, 87967929181, 11389176⟩,
    ⟨88360, 88801, 87967929181, 88343936296, 11394155⟩,
    ⟨88801, 89245, 88343936296, 88845498544, 11399142⟩,
    ⟨89245, 89691, 88845498544, 89347280132, 11404127⟩,
    ⟨89691, 90139, 89347280132, 89815053642, 11409110⟩,
    ⟨90139, 90589, 89815053642, 90260203152, 11414090⟩,
    ⟨90589, 91041, 90260203152, 90682708631, 11419067⟩,
    ⟨91041, 91496, 90682708631, 91162518815, 11424052⟩,
    ⟨91496, 91953, 91162518815, 91562535005, 11429034⟩,
    ⟨91953, 92412, 91562535005, 92077065635, 11434014⟩,
    ⟨92412, 92874, 92077065635, 92614698682, 11439001⟩,
    ⟨92874, 93338, 92614698682, 93106789994, 11443984⟩,
    ⟨93338, 93804, 93106789994, 93484605806, 11448964⟩,
    ⟨93804, 94273, 93484605806, 93965671790, 11453952⟩,
    ⟨94273, 94744, 93965671790, 94446947060, 11458935⟩,
    ⟨94744, 95217, 94446947060, 94951359320, 11463915⟩,
    ⟨95217, 95693, 94951359320, 95444522106, 11468902⟩,
    ⟨95693, 96171, 95444522106, 95937899161, 11473885⟩,
    ⟨96171, 96651, 95937899161, 96397053681, 11478863⟩,
    ⟨96651, 97134, 96397053681, 96879375297, 11483848⟩,
    ⟨97134, 97619, 96879375297, 97373394944, 11488829⟩,
    ⟨97619, 98107, 97373394944, 97798666099, 11493815⟩,
    ⟨98107, 98597, 97798666099, 98270116817, 11498798⟩,
    ⟨98597, 99089, 98270116817, 98799290467, 11503775⟩,
    ⟨99089, 99584, 98799290467, 99294167061, 11508758⟩,
    ⟨99584, 100081, 99294167061, 99777744015, 11513737⟩,
    ⟨100081, 100581, 99777744015, 100273048975, 11518720⟩,
    ⟨100581, 101083, 100273048975, 100710949537, 11523699⟩,
    ⟨101083, 101588, 100710949537, 101287383637, 11528682⟩,
    ⟨101588, 102095, 101287383637, 101840999365, 11533661⟩,
    ⟨102095, 102605, 101840999365, 102383315586, 11538643⟩,
    ⟨102605, 103118, 102383315586, 102845060826, 11543631⟩,
    ⟨103118, 103633, 102845060826, 103283908120, 11548613⟩,
    ⟨103633, 104151, 103283908120, 103815373674, 11553599⟩,
    ⟨104151, 104671, 103815373674, 104300833992, 11558579⟩,
    ⟨104671, 105194, 104300833992, 104821194327, 11563563⟩,
    ⟨105194, 105719, 104821194327, 105388052836, 11568541⟩,
    ⟨105719, 106247, 105388052836, 105862567279, 11573523⟩,
    ⟨106247, 106778, 105862567279, 106464649747, 11578509⟩,
    ⟨106778, 107311, 106464649747, 106997490195, 11583488⟩,
    ⟨107311, 107847, 106997490195, 107437852055, 11588470⟩,
    ⟨107847, 108386, 107437852055, 108005931399, 11593456⟩,
    ⟨108386, 108927, 108005931399, 108539459409, 11598435⟩,
    ⟨108927, 109471, 108539459409, 109142837041, 11603416⟩,
    ⟨109471, 110018, 109142837041, 109676823487, 11608401⟩,
    ⟨110018, 110568, 109676823487, 110152972354, 11613387⟩,
    ⟨110568, 111120, 110152972354, 110733890704, 11618367⟩,
    ⟨111120, 111675, 110733890704, 111268564804, 11623350⟩,
    ⟨111675, 112233, 111268564804, 111826724836, 11628334⟩,
    ⟨112233, 112794, 111826724836, 112350224236, 11633320⟩,
    ⟨112794, 113357, 112350224236, 112990330681, 11638299⟩,
    ⟨113357, 113923, 112990330681, 113490991721, 11643280⟩,
    ⟨113923, 114492, 113490991721, 114038460035, 11648262⟩,
    ⟨114492, 115064, 114038460035, 114597815795, 11653245⟩,
    ⟨115064, 115639, 114597815795, 115169069065, 11658230⟩,
    ⟨115639, 116217, 115169069065, 115810545945, 11663216⟩,
    ⟨116217, 116798, 115810545945, 116335615080, 11668203⟩,
    ⟨116798, 117381, 116335615080, 116942620544, 11673182⟩,
    ⟨117381, 117967, 116942620544, 117549884968, 11678162⟩,
    ⟨117967, 118556, 117549884968, 118098992642, 11683142⟩,
    ⟨118556, 119148, 118098992642, 118695086915, 11688123⟩,
    ⟨119148, 119743, 118695086915, 119256355955, 11693105⟩,
    ⟨119743, 120341, 119256355955, 119876354513, 11698086⟩,
    ⟨120341, 120942, 119876354513, 120531726321, 11703068⟩,
    ⟨120942, 121546, 120531726321, 121152252971, 11708050⟩,
    ⟨121546, 122153, 121152252971, 121773043614, 11713031⟩,
    ⟨122153, 122763, 121773043614, 122394098250, 11718012⟩,
    ⟨122763, 123376, 122394098250, 122945078921, 11722993⟩,
    ⟨123376, 123992, 122945078921, 123637029387, 11727974⟩,
    ⟨123992, 124611, 123637029387, 124235410041, 11732954⟩,
    ⟨124611, 125234, 124235410041, 124869258855, 11737941⟩,
    ⟨125234, 125860, 124869258855, 125479891059, 11742927⟩,
    ⟨125860, 126489, 125479891059, 126126026219, 11747912⟩,
    ⟨126489, 127121, 126126026219, 126666659435, 11752896⟩,
    ⟨127121, 127756, 126666659435, 127372132175, 11757879⟩,
    ⟨127756, 128394, 127372132175, 127983800895, 11762860⟩,
    ⟨128394, 129035, 127983800895, 128678103455, 11767840⟩,
    ⟨129035, 129680, 128678103455, 129360927421, 11772827⟩,
    ⟨129680, 130328, 129360927421, 129949817971, 11777811⟩,
    ⟨130328, 130979, 129949817971, 130597871641, 11782794⟩,
    ⟨130979, 131072, 130597871641, 130703923177, 11783504⟩
  ]⟩,
  ⟨131072, 262144, [
    ⟨131072, 131727, 130703923177, 131316924553, 11788488⟩,
    ⟨131727, 132385, 131316924553, 131977358929, 11793471⟩,
    ⟨132385, 133046, 131977358929, 132661669145, 11798452⟩,
    ⟨133046, 133711, 132661669145, 133346268549, 11803438⟩,
    ⟨133711, 134379, 133346268549, 134019348546, 11808421⟩,
    ⟨134379, 135050, 134019348546, 134610018646, 11813402⟩,
    ⟨135050, 135725, 134610018646, 135354577090, 11818388⟩,
    ⟨135725, 136403, 135354577090, 136052155979, 11823371⟩,
    ⟨136403, 137085, 136052155979, 136750029101, 11828358⟩,
    ⟨137085, 137770, 136750029101, 137436362937, 11833342⟩,
    ⟨137770, 138458, 137436362937, 138146662377, 11838324⟩,
    ⟨138458, 139150, 138146662377, 138786201063, 11843309⟩,
    ⟨139150, 139845, 138786201063, 139497098523, 11848291⟩,
    ⟨139845, 140544, 139497098523, 140196441866, 11853277⟩,
    ⟨140544, 141246, 140196441866, 140943512246, 11858260⟩,
    ⟨141246, 141952, 140943512246, 141690896744, 11863246⟩,
    ⟨141952, 142661, 141690896744, 142379253968, 11868228⟩,
    ⟨142661, 143374, 142379253968, 142984787831, 11873213⟩,
    ⟨143374, 144090, 142984787831, 143697479531, 11878195⟩,
    ⟨144090, 144810, 143697479531, 144386703913, 11883179⟩,
    ⟨144810, 145534, 144386703913, 145099993933, 11888167⟩,
    ⟨145534, 146261, 145099993933, 145849262320, 11893149⟩,
    ⟨146261, 146992, 145849262320, 146575048555, 11898135⟩,
    ⟨146992, 147726, 146575048555, 147313041747, 11903116⟩,
    ⟨147726, 148464, 147313041747, 147991803390, 11908099⟩,
    ⟨148464, 149206, 147991803390, 148813806255, 11913085⟩,
    ⟨149206, 149952, 148813806255, 149588480935, 11918072⟩,
    ⟨149952, 150701, 149588480935, 150339633400, 11923055⟩,
    ⟨150701, 151454, 150339633400, 151114955935, 11928039⟩,
    ⟨151454, 152211, 151114955935, 151938334591, 11933024⟩,
    ⟨152211, 152972, 151938334591, 152738181395, 11938012⟩,
    ⟨152972, 153736, 152738181395, 153454761035, 11942994⟩,
    ⟨153736, 154504, 153454761035, 154219431563, 11947977⟩,
    ⟨154504, 155276, 154219431563, 154972468106, 11952961⟩,
    ⟨155276, 156052, 154972468106, 155761692542, 11957946⟩,
    ⟨156052, 156832, 155761692542, 156491431394, 11962932⟩,
    ⟨156832, 157616, 156491431394, 157305249818, 11967918⟩,
    ⟨157616, 158404, 157305249818, 158047569990, 11972906⟩,
    ⟨158404, 159196, 158047569990, 158790199356, 11977893⟩,
    ⟨159196, 159991, 158790199356, 159617017662, 11982874⟩,
    ⟨159991, 160790, 159617017662, 160444179726, 11987856⟩,
    ⟨160790, 161593, 160444179726, 161223714196, 11992838⟩,
    ⟨161593, 162400, 161223714196, 161943583336, 11997819⟩,
    ⟨162400, 163212, 161943583336, 162831791054, 12002807⟩,
    ⟨163212, 164028, 162831791054, 163636313252, 12007794⟩,
    ⟨164028, 164848, 163636313252, 164453182360, 12012781⟩,
    ⟨164848, 165672, 164453182360, 165198283914, 12017767⟩,
    ⟨165672, 166500, 165198283914, 165955717290, 12022752⟩,
    ⟨166500, 167332, 165955717290, 166869825302, 12027737⟩,
    ⟨167332, 168168, 166869825302, 167627886662, 12032720⟩,
    ⟨168168, 169008, 167627886662, 168374224248, 12037703⟩,
    ⟨169008, 169853, 168374224248, 169241297928, 12042690⟩,
    ⟨169853, 170702, 169241297928, 170132825952, 12047676⟩,
    ⟨170702, 171555, 170132825952, 170976512222, 12052661⟩,
    ⟨171555, 172412, 170976512222, 171868777878, 12057644⟩,
    ⟨172412, 173274, 171868777878, 172761412572, 12062631⟩,
    ⟨173274, 174140, 172761412572, 173618213308, 12067616⟩,
    ⟨174140, 175010, 173618213308, 174463295308, 12072600⟩,
    ⟨175010, 175885, 174463295308, 175212105702, 12077587⟩,
    ⟨175885, 176764, 175212105702, 176251206894, 12082572⟩,
    ⟨176764, 177647, 176251206894, 177061073079, 12087555⟩,
    ⟨177647, 178535, 177061073079, 177931736031, 12092541⟩,
    ⟨178535, 179427, 177931736031, 178899538031, 12097525⟩,
    ⟨179427, 180324, 178899538031, 179928251551, 12102512⟩,
    ⟨180324, 181225, 179928251551, 180691023799, 12107496⟩,
    ⟨181225, 182131, 180691023799, 181611572507, 12112483⟩,
    ⟨182131, 183041, 181611572507, 182556734933, 12117467⟩,
    ⟨183041, 183956, 182556734933, 183429551549, 12122453⟩,
    ⟨183956, 184875, 183429551549, 184351236761, 12127437⟩,
    ⟨184875, 185799, 184351236761, 185346095365, 12132422⟩,
    ⟨185799, 186727, 185346095365, 186329225089, 12137404⟩,
    ⟨186727, 187660, 186329225089, 187288473820, 12142389⟩,
    ⟨187660, 188598, 187288473820, 188126642695, 12147375⟩,
    ⟨188598, 189540, 188126642695, 189147440683, 12152357⟩,
    ⟨189540, 190487, 189147440683, 190022769235, 12157341⟩,
    ⟨190487, 191439, 190022769235, 190910619033, 12162326⟩,
    ⟨191439, 192396, 190910619033, 191993509890, 12167313⟩,
    ⟨192396, 193357, 191993509890, 192942948900, 12172295⟩,
    ⟨193357, 194323, 192942948900, 193941485778, 12177279⟩,
    ⟨194323, 195294, 193941485778, 194879520029, 12182263⟩,
    ⟨195294, 196270, 194879520029, 195830125373, 12187248⟩,
    ⟨196270, 197251, 195830125373, 196768927391, 12192234⟩,
    ⟨197251, 198237, 196768927391, 197793493871, 12197220⟩,
    ⟨198237, 199228, 197793493871, 198794074845, 12202207⟩,
    ⟨199228, 200224, 198794074845, 199782857559, 12207194⟩,
    ⟨200224, 201225, 199782857559, 200723195419, 12212180⟩,
    ⟨201225, 202231, 200723195419, 201786088948, 12217167⟩,
    ⟨202231, 203242, 201786088948, 202714972652, 12222154⟩,
    ⟨203242, 204258, 202714972652, 203693143932, 12227141⟩,
    ⟨204258, 205279, 203693143932, 204708410473, 12232127⟩,
    ⟨205279, 206305, 204708410473, 205821987665, 12237112⟩,
    ⟨206305, 207336, 205821987665, 206789113328, 12242097⟩,
    ⟨207336, 208372, 206789113328, 207903597790, 12247082⟩,
    ⟨208372, 209413, 207903597790, 208994031575, 12252065⟩,
    ⟨209413, 210460, 208994031575, 210146194463, 12257052⟩,
    ⟨210460, 211512, 210146194463, 211212991856, 12262039⟩,
    ⟨211512, 212569, 211212991856, 212169819650, 12267023⟩,
    ⟨212569, 213631, 212169819650, 213212940245, 12272007⟩,
    ⟨213631, 214699, 213212940245, 214305592711, 12276994⟩,
    ⟨214699, 215772, 214305592711, 215300433010, 12281979⟩,
    ⟨215772, 216850, 215300433010, 216307963976, 12286963⟩,
    ⟨216850, 217934, 216307963976, 217389655488, 12291949⟩,
    ⟨217934, 219023, 217389655488, 218508676482, 12296934⟩,
    ⟨219023, 220118, 218508676482, 219665057056, 12301921⟩,
    ⟨220118, 221218, 219665057056, 220760371601, 12306905⟩,
    ⟨221218, 222324, 220760371601, 221880753864, 12311893⟩,
    ⟨222324, 223435, 221880753864, 223026223425, 12316877⟩,
    ⟨223435, 224552, 223026223425, 224085903729, 12321864⟩,
    ⟨224552, 225674, 224085903729, 225244627441, 12326848⟩,
    ⟨225674, 226802, 225244627441, 226354492501, 12331834⟩,
    ⟨226802, 227936, 226354492501, 227440132837, 12336822⟩,
    ⟨227936, 229075, 227440132837, 228637288019, 12341806⟩,
    ⟨229075, 230220, 228637288019, 229909007595, 12346792⟩,
    ⟨230220, 231371, 229909007595, 231070074821, 12351779⟩,
    ⟨231371, 232527, 231070074821, 232182183491, 12356763⟩,
    ⟨232527, 233689, 232182183491, 233257655567, 12361748⟩,
    ⟨233689, 234857, 233257655567, 234420128563, 12366734⟩,
    ⟨234857, 236031, 234420128563, 235508839923, 12371720⟩,
    ⟨236031, 237211, 235508839923, 236647496967, 12376707⟩,
    ⟨237211, 238397, 236647496967, 237811376203, 12381694⟩,
    ⟨238397, 239588, 237811376203, 238988110613, 12386678⟩,
    ⟨239588, 240785, 238988110613, 240165318408, 12391661⟩,
    ⟨240785, 241988, 240165318408, 241491759423, 12396645⟩,
    ⟨241988, 243197, 241491759423, 242632709291, 12401629⟩,
    ⟨243197, 244412, 242632709291, 243873370491, 12406612⟩,
    ⟨244412, 245634, 243873370491, 245114530391, 12411599⟩,
    ⟨245634, 246862, 245114530391, 246368605577, 12416586⟩,
    ⟨246862, 248096, 246368605577, 247623184450, 12421573⟩,
    ⟨248096, 249336, 247623184450, 248915546482, 12426558⟩,
    ⟨249336, 250582, 248915546482, 250034385352, 12431543⟩,
    ⟨250582, 251834, 250034385352, 251389966795, 12436527⟩,
    ⟨251834, 253093, 251389966795, 252609235167, 12441514⟩,
    ⟨253093, 254358, 252609235167, 253866331667, 12446500⟩,
    ⟨254358, 255629, 253866331667, 255173737487, 12451484⟩,
    ⟨255629, 256907, 255173737487, 256419384587, 12456471⟩,
    ⟨256907, 258191, 256419384587, 257653068731, 12461456⟩,
    ⟨258191, 259481, 257653068731, 258949578491, 12466440⟩,
    ⟨259481, 260778, 258949578491, 260209192517, 12471426⟩,
    ⟨260778, 262081, 260209192517, 261419404287, 12476410⟩,
    ⟨262081, 262144, 261419404287, 261506740844, 12476651⟩
  ]⟩,
  ⟨262144, 524288, [
    ⟨262144, 263454, 261506740844, 262817312624, 12481636⟩,
    ⟨263454, 264771, 262817312624, 264115921312, 12486622⟩,
    ⟨264771, 266094, 264115921312, 265514981184, 12491606⟩,
    ⟨266094, 267424, 265514981184, 266852116528, 12496592⟩,
    ⟨267424, 268761, 266852116528, 268227290218, 12501579⟩,
    ⟨268761, 270104, 268227290218, 269628025386, 12506564⟩,
    ⟨270104, 271454, 269628025386, 271016807325, 12511549⟩,
    ⟨271454, 272811, 271016807325, 272406142821, 12516536⟩,
    ⟨272811, 274175, 272406142821, 273670816644, 12521523⟩,
    ⟨274175, 275545, 273670816644, 275048732524, 12526508⟩,
    ⟨275545, 276922, 275048732524, 276502385712, 12531493⟩,
    ⟨276922, 278306, 276502385712, 277793642946, 12536478⟩,
    ⟨278306, 279697, 277793642946, 279173203986, 12541464⟩,
    ⟨279697, 281095, 279173203986, 280590952723, 12546449⟩,
    ⟨281095, 282500, 280590952723, 282084573488, 12551435⟩,
    ⟨282500, 283912, 282084573488, 283390441272, 12556421⟩,
    ⟨283912, 285331, 283390441272, 284910371519, 12561407⟩,
    ⟨285331, 286757, 284910371519, 286267541855, 12566392⟩,
    ⟨286757, 288190, 286267541855, 287474394047, 12571377⟩,
    ⟨288190, 289630, 287474394047, 289008710089, 12576361⟩,
    ⟨289630, 291078, 289008710089, 290505890501, 12581348⟩,
    ⟨291078, 292533, 290505890501, 291915559909, 12586334⟩,
    ⟨292533, 293995, 291915559909, 293225057189, 12591320⟩,
    ⟨293995, 295464, 293225057189, 294761806277, 12596304⟩,
    ⟨295464, 296941, 294761806277, 296223555917, 12601290⟩,
    ⟨296941, 298425, 296223555917, 297635458717, 12606275⟩,
    ⟨298425, 299917, 297635458717, 299022697647, 12611263⟩,
    ⟨299917, 301416, 299022697647, 300587112399, 12616248⟩,
    ⟨301416, 302923, 300587112399, 302025933189, 12621235⟩,
    ⟨302923, 304437, 302025933189, 303667341919, 12626221⟩,
    ⟨304437, 305959, 303667341919, 305296767751, 12631208⟩,
    ⟨305959, 307488, 305296767751, 306863655683, 12636193⟩,
    ⟨307488, 309025, 306863655683, 308292108910, 12641179⟩,
    ⟨309025, 310570, 308292108910, 309822294996, 12646166⟩,
    ⟨310570, 312122, 309822294996, 311289828512, 12651151⟩,
    ⟨312122, 313682, 311289828512, 312922470185, 12656137⟩,
    ⟨313682, 315250, 312922470185, 314479788314, 12661123⟩,
    ⟨315250, 316826, 314479788314, 316126382614, 12666110⟩,
    ⟨316826, 318410, 316126382614, 317811638515, 12671097⟩,
    ⟨318410, 320002, 317811638515, 319484881603, 12676084⟩,
    ⟨320002, 321602, 319484881603, 321108058819, 12681072⟩,
    ⟨321602, 323210, 321108058819, 322719188312, 12686059⟩,
    ⟨323210, 324826, 322719188312, 324330951154, 12691046⟩,
    ⟨324826, 326450, 324330951154, 325981435574, 12696034⟩,
    ⟨326450, 328082, 325981435574, 327721475314, 12701020⟩,
    ⟨328082, 329722, 327721475314, 329322432196, 12706007⟩,
    ⟨329722, 331370, 329322432196, 331012994132, 12710992⟩,
    ⟨331370, 333026, 331012994132, 332589775280, 12715977⟩,
    ⟨333026, 334691, 332589775280, 334256221564, 12720964⟩,
    ⟨334691, 336364, 334256221564, 335923321145, 12725951⟩,
    ⟨336364, 338045, 335923321145, 337680190313, 12730936⟩,
    ⟨338045, 339735, 337680190313, 339272180688, 12735923⟩,
    ⟨339735, 341433, 339272180688, 340953980544, 12740908⟩,
    ⟨341433, 343140, 340953980544, 342623692789, 12745895⟩,
    ⟨343140, 344855, 342623692789, 344383314367, 12750881⟩,
    ⟨344855, 346579, 344383314367, 346181891755, 12755868⟩,
    ⟨346579, 348311, 346181891755, 347904606910, 12760853⟩,
    ⟨348311, 350052, 347904606910, 349679058392, 12765838⟩,
    ⟨350052, 351802, 349679058392, 351415890592, 12770825⟩,
    ⟨351802, 353561, 351415890592, 353178952786, 12775813⟩,
    ⟨353561, 355328, 353178952786, 355044949294, 12780798⟩,
    ⟨355328, 357104, 355044949294, 356681529646, 12785784⟩,
    ⟨357104, 358889, 356681529646, 358548982066, 12790770⟩,
    ⟨358889, 360683, 358548982066, 360174043078, 12795756⟩,
    ⟨360683, 362486, 360174043078, 362042951556, 12800743⟩,
    ⟨362486, 364298, 362042951556, 363784530700, 12805729⟩,
    ⟨364298, 366119, 363784530700, 365616462945, 12810715⟩,
    ⟨366119, 367949, 365616462945, 367590080899, 12815701⟩,
    ⟨367949, 369788, 367590080899, 369154204713, 12820687⟩,
    ⟨369788, 371636, 369154204713, 370949798793, 12825672⟩,
    ⟨371636, 373494, 370949798793, 372823075007, 12830659⟩,
    ⟨373494, 375361, 372823075007, 374735586112, 12835645⟩,
    ⟨375361, 377237, 374735586112, 376623158722, 12840630⟩,
    ⟨377237, 379123, 376623158722, 378460081953, 12845617⟩,
    ⟨379123, 381018, 378460081953, 380336269991, 12850603⟩,
    ⟨381018, 382923, 380336269991, 382174619504, 12855591⟩,
    ⟨382923, 384837, 382174619504, 384155148362, 12860577⟩,
    ⟨384837, 386761, 384155148362, 386149310782, 12865564⟩,
    ⟨386761, 388694, 386149310782, 387861093799, 12870549⟩,
    ⟨388694, 390637, 387861093799, 389908304023, 12875536⟩,
    ⟨390637, 392590, 389908304023, 391982068226, 12880523⟩,
    ⟨392590, 394552, 391982068226, 394030863998, 12885508⟩,
    ⟨394552, 396524, 394030863998, 395951547455, 12890493⟩,
    ⟨396524, 398506, 395951547455, 397963242179, 12895479⟩,
    ⟨398506, 400498, 397963242179, 399962814409, 12900466⟩,
    ⟨400498, 402500, 399962814409, 401769577689, 12905452⟩,
    ⟨402500, 404512, 401769577689, 403796516455, 12910438⟩,
    ⟨404512, 406534, 403796516455, 405682168359, 12915424⟩,
    ⟨406534, 408566, 405682168359, 407723593139, 12920410⟩,
    ⟨408566, 410608, 407723593139, 409791656499, 12925396⟩,
    ⟨410608, 412661, 409791656499, 411925169694, 12930383⟩,
    ⟨412661, 414724, 411925169694, 413904281304, 12935370⟩,
    ⟨414724, 416797, 413904281304, 415961797908, 12940356⟩,
    ⟨416797, 418880, 415961797908, 418123669855, 12945341⟩,
    ⟨418880, 420974, 418123669855, 420195722335, 12950328⟩,
    ⟨420974, 423078, 420195722335, 422255617102, 12955313⟩,
    ⟨423078, 425193, 422255617102, 424458868102, 12960300⟩,
    ⟨425193, 427318, 424458868102, 426481452562, 12965285⟩,
    ⟨427318, 429454, 426481452562, 428556695922, 12970271⟩,
    ⟨429454, 431601, 428556695922, 430827366072, 12975258⟩,
    ⟨431601, 433759, 430827366072, 433189770844, 12980246⟩,
    ⟨433759, 435927, 433189770844, 435501142140, 12985232⟩,
    ⟨435927, 438106, 435501142140, 437501635712, 12990218⟩,
    ⟨438106, 440296, 437501635712, 439645844372, 12995204⟩,
    ⟨440296, 442497, 439645844372, 441881877052, 13000190⟩,
    ⟨442497, 444709, 441881877052, 444339855505, 13005177⟩,
    ⟨444709, 446932, 444339855505, 446369440933, 13010163⟩,
    ⟨446932, 449166, 446369440933, 448451864773, 13015149⟩,
    ⟨449166, 451411, 448451864773, 450899650153, 13020135⟩,
    ⟨451411, 453668, 450899650153, 452957619429, 13025122⟩,
    ⟨453668, 455936, 452957619429, 455211828286, 13030109⟩,
    ⟨455936, 458215, 455211828286, 457466899721, 13035095⟩,
    ⟨458215, 460506, 457466899721, 459605473333, 13040083⟩,
    ⟨460506, 462808, 459605473333, 461810089994, 13045069⟩,
    ⟨462808, 465122, 461810089994, 464276550767, 13050057⟩,
    ⟨465122, 467447, 464276550767, 466391467733, 13055043⟩,
    ⟨467447, 469784, 466391467733, 468885933463, 13060030⟩,
    ⟨469784, 472132, 468885933463, 471394416343, 13065015⟩,
    ⟨472132, 474492, 471394416343, 473733946701, 13070002⟩,
    ⟨474492, 476864, 473733946701, 476270494373, 13074988⟩,
    ⟨476864, 479248, 476270494373, 478624889873, 13079975⟩,
    ⟨479248, 481644, 478624889873, 481006352957, 13084962⟩,
    ⟨481644, 484052, 481006352957, 483454173420, 13089949⟩,
    ⟨484052, 486472, 483454173420, 485588647988, 13094936⟩,
    ⟨486472, 488904, 485588647988, 488195532665, 13099923⟩,
    ⟨488904, 491348, 488195532665, 490659255557, 13104909⟩,
    ⟨491348, 493804, 490659255557, 493045256447, 13109895⟩,
    ⟨493804, 496273, 493045256447, 495668233047, 13114883⟩,
    ⟨496273, 498754, 495668233047, 498095408997, 13119870⟩,
    ⟨498754, 501247, 498095408997, 500786004477, 13124856⟩,
    ⟨501247, 503753, 500786004477, 503018077787, 13129843⟩,
    ⟨503753, 506271, 503018077787, 505605639100, 13134829⟩,
    ⟨506271, 508802, 505605639100, 508089064324, 13139816⟩,
    ⟨508802, 511346, 508089064324, 510665445712, 13144803⟩,
    ⟨511346, 513902, 510665445712, 513190205200, 13149789⟩,
    ⟨513902, 516471, 513190205200, 515742231744, 13154776⟩,
    ⟨516471, 519053, 515742231744, 518453142922, 13159763⟩,
    ⟨519053, 521648, 518453142922, 521099257672, 13164750⟩,
    ⟨521648, 524256, 521099257672, 523720035335, 13169737⟩,
    ⟨524256, 524288, 523720035335, 523772714527, 13169798⟩
  ]⟩,
  ⟨524288, 1048576, [
    ⟨524288, 526909, 523772714527, 526486720237, 13174785⟩,
    ⟨526909, 529543, 526486720237, 529043595811, 13179771⟩,
    ⟨529543, 532190, 529043595811, 531640992940, 13184757⟩,
    ⟨532190, 534850, 531640992940, 534292131283, 13189743⟩,
    ⟨534850, 537524, 534292131283, 536970661473, 13194730⟩,
    ⟨537524, 540211, 536970661473, 539557806005, 13199717⟩,
    ⟨540211, 542912, 539557806005, 542251565621, 13204704⟩,
    ⟨542912, 545626, 542251565621, 544906713512, 13209691⟩,
    ⟨545626, 548354, 544906713512, 547536434434, 13214678⟩,
    ⟨548354, 551095, 547536434434, 550418321186, 13219664⟩,
    ⟨551095, 553850, 550418321186, 553155823943, 13224651⟩,
    ⟨553850, 556619, 553155823943, 555788521905, 13229638⟩,
    ⟨556619, 559402, 555788521905, 558554558530, 13234625⟩,
    ⟨559402, 562199, 558554558530, 561281918808, 13239613⟩,
    ⟨562199, 565009, 561281918808, 564142751976, 13244598⟩,
    ⟨565009, 567834, 564142751976, 566872166692, 13249586⟩,
    ⟨567834, 570673, 566872166692, 569880954763, 13254573⟩,
    ⟨570673, 573526, 569880954763, 572798057963, 13259560⟩,
    ⟨573526, 576393, 572798057963, 575610141715, 13264546⟩,
    ⟨576393, 579274, 575610141715, 578489630159, 13269532⟩,
    ⟨579274, 582170, 578489630159, 581476396934, 13274519⟩,
    ⟨582170, 585080, 581476396934, 584411167539, 13279505⟩,
    ⟨585080, 588005, 584411167539, 587546307651, 13284492⟩,
    ⟨588005, 590945, 587546307651, 590310519491, 13289480⟩,
    ⟨590945, 593899, 590310519491, 593248596477, 13294466⟩,
    ⟨593899, 596868, 593248596477, 596307470667, 13299453⟩,
    ⟨596868, 599852, 596307470667, 599194534147, 13304440⟩,
    ⟨599852, 602851, 599194534147, 602282321211, 13309427⟩,
    ⟨602851, 605865, 602282321211, 605238121119, 13314414⟩,
    ⟨605865, 608894, 605238121119, 608314902750, 13319401⟩,
    ⟨608894, 611938, 608314902750, 611326214438, 13324388⟩,
    ⟨611938, 614997, 611326214438, 614445287954, 13329374⟩,
    ⟨614997, 618071, 614445287954, 617725540514, 13334360⟩,
    ⟨618071, 621161, 617725540514, 620726893589, 13339347⟩,
    ⟨621161, 624266, 620726893589, 623769401513, 13344333⟩,
    ⟨624266, 627387, 623769401513, 626772998513, 13349320⟩,
    ⟨627387, 630523, 626772998513, 629697591527, 13354306⟩,
    ⟨630523, 633675, 629697591527, 632903821847, 13359293⟩,
    ⟨633675, 636843, 632903821847, 636164706167, 13364280⟩,
    ⟨636843, 640027, 636164706167, 639105944907, 13369267⟩,
    ⟨640027, 643227, 639105944907, 642182023327, 13374254⟩,
    ⟨643227, 646443, 642182023327, 645500075343, 13379242⟩,
    ⟨646443, 649675, 645500075343, 648805979906, 13384229⟩,
    ⟨649675, 652923, 648805979906, 652006002530, 13389216⟩,
    ⟨652923, 656187, 652006002530, 655220611250, 13394203⟩,
    ⟨656187, 659467, 655220611250, 658423017421, 13399189⟩,
    ⟨659467, 662764, 658423017421, 661787465597, 13404176⟩,
    ⟨662764, 666077, 661787465597, 665233620231, 13409162⟩,
    ⟨666077, 669407, 665233620231, 668385945246, 13414149⟩,
    ⟨669407, 672754, 668385945246, 671713891222, 13419137⟩,
    ⟨672754, 676117, 671713891222, 675217587325, 13424123⟩,
    ⟨676117, 679497, 675217587325, 678507719275, 13429110⟩,
    ⟨679497, 682894, 678507719275, 681987150139, 13434096⟩,
    ⟨682894, 686308, 681987150139, 685400677221, 13439083⟩,
    ⟨686308, 689739, 685400677221, 688869247281, 13444070⟩,
    ⟨689739, 693187, 688869247281, 692325654930, 13449057⟩,
    ⟨693187, 696652, 692325654930, 695783343981, 13454043⟩,
    ⟨696652, 700135, 695783343981, 699175019541, 13459030⟩,
    ⟨700135, 703635, 699175019541, 702648735927, 13464017⟩,
    ⟨703635, 707153, 702648735927, 706366181031, 13469004⟩,
    ⟨707153, 710688, 706366181031, 709990684341, 13473990⟩,
    ⟨710688, 714241, 709990684341, 713508697338, 13478977⟩,
    ⟨714241, 717812, 713508697338, 716987560050, 13483964⟩,
    ⟨717812, 721401, 716987560050, 720643066042, 13488952⟩,
    ⟨721401, 725008, 720643066042, 724286429572, 13493939⟩,
    ⟨725008, 728633, 724286429572, 727782651665, 13498927⟩,
    ⟨728633, 732276, 727782651665, 731563747585, 13503914⟩,
    ⟨732276, 735937, 731563747585, 735224659756, 13508901⟩,
    ⟨735937, 739616, 735224659756, 738954492844, 13513888⟩,
    ⟨739616, 743314, 738954492844, 742564032469, 13518875⟩,
    ⟨743314, 747030, 742564032469, 745917950245, 13523862⟩,
    ⟨747030, 750765, 745917950245, 749570739475, 13528849⟩,
    ⟨750765, 754518, 749570739475, 753536153423, 13533836⟩,
    ⟨754518, 758290, 753536153423, 757110402695, 13538823⟩,
    ⟨758290, 762081, 757110402695, 761132914265, 13543810⟩,
    ⟨762081, 765891, 761132914265, 764967223816, 13548797⟩,
    ⟨765891, 769720, 764967223816, 768843606040, 13553784⟩,
    ⟨769720, 773568, 768843606040, 772694296720, 13558770⟩,
    ⟨773568, 777435, 772694296720, 776519276194, 13563757⟩,
    ⟨777435, 781322, 776519276194, 780413505722, 13568744⟩,
    ⟨781322, 785228, 780413505722, 784377035174, 13573731⟩,
    ⟨785228, 789154, 784377035174, 788382756984, 13578718⟩,
    ⟨789154, 793099, 788382756984, 792294864024, 13583705⟩,
    ⟨793099, 797064, 792294864024, 796466592468, 13588692⟩,
    ⟨797064, 801049, 796466592468, 800463134094, 13593679⟩,
    ⟨801049, 805054, 800463134094, 804311556572, 13598666⟩,
    ⟨805054, 809079, 804311556572, 808188597677, 13603653⟩,
    ⟨809079, 813124, 808188597677, 812339232877, 13608640⟩,
    ⟨813124, 817189, 812339232877, 816423320977, 13613627⟩,
    ⟨817189, 821274, 816423320977, 820481667949, 13618614⟩,
    ⟨821274, 825380, 820481667949, 824800349466, 13623601⟩,
    ⟨825380, 829506, 824800349466, 828820782631, 13628587⟩,
    ⟨829506, 833653, 828820782631, 833128992015, 13633574⟩,
    ⟨833653, 837821, 833128992015, 837097813266, 13638561⟩,
    ⟨837821, 842010, 837097813266, 841177234417, 13643549⟩,
    ⟨842010, 846220, 841177234417, 845394632041, 13648536⟩,
    ⟨846220, 850451, 845394632041, 849750106197, 13653524⟩,
    ⟨850451, 854703, 849750106197, 853806683964, 13658511⟩,
    ⟨854703, 858976, 853806683964, 858097022336, 13663498⟩,
    ⟨858976, 863270, 858097022336, 862484605700, 13668484⟩,
    ⟨863270, 867586, 862484605700, 866901136833, 13673471⟩,
    ⟨867586, 871923, 866901136833, 871182494187, 13678458⟩,
    ⟨871923, 876282, 871182494187, 875656980702, 13683445⟩,
    ⟨876282, 880663, 875656980702, 880037278942, 13688432⟩,
    ⟨880663, 885066, 880037278942, 884364399346, 13693419⟩,
    ⟨885066, 889491, 884364399346, 888939666950, 13698406⟩,
    ⟨889491, 893938, 888939666950, 893297345924, 13703393⟩,
    ⟨893938, 898407, 893297345924, 897807402944, 13708380⟩,
    ⟨898407, 902899, 897807402944, 902099686815, 13713367⟩,
    ⟨902899, 907413, 902099686815, 906709053759, 13718354⟩,
    ⟨907413, 911950, 906709053759, 911457330091, 13723342⟩,
    ⟨911950, 916509, 911457330091, 915768025397, 13728329⟩,
    ⟨916509, 921091, 915768025397, 920368686257, 13733316⟩,
    ⟨921091, 925696, 920368686257, 925204568913, 13738303⟩,
    ⟨925696, 930324, 925204568913, 929794827773, 13743290⟩,
    ⟨930324, 934975, 929794827773, 934400500568, 13748277⟩,
    ⟨934975, 939649, 934400500568, 938897817569, 13753263⟩,
    ⟨939649, 944347, 938897817569, 943685688569, 13758250⟩,
    ⟨944347, 949068, 943685688569, 948213793542, 13763237⟩,
    ⟨949068, 953813, 948213793542, 952950062598, 13768224⟩,
    ⟨953813, 958582, 952950062598, 957577861830, 13773212⟩,
    ⟨958582, 963374, 957577861830, 962469122120, 13778198⟩,
    ⟨963374, 968190, 962469122120, 967210537760, 13783185⟩,
    ⟨968190, 973030, 967210537760, 972201856024, 13788172⟩,
    ⟨973030, 977895, 972201856024, 976863943766, 13793159⟩,
    ⟨977895, 982784, 976863943766, 981624304136, 13798146⟩,
    ⟨982784, 987697, 981624304136, 986496810085, 13803133⟩,
    ⟨987697, 992635, 986496810085, 991371076445, 13808120⟩,
    ⟨992635, 997598, 991371076445, 996343794965, 13813107⟩,
    ⟨997598, 1002585, 996343794965, 1001442671651, 13818094⟩,
    ⟨1002585, 1007597, 1001442671651, 1006460449691, 13823080⟩,
    ⟨1007597, 1012634, 1006460449691, 1011756599352, 13828067⟩,
    ⟨1012634, 1017697, 1011756599352, 1016764164900, 13833054⟩,
    ⟨1017697, 1022785, 1016764164900, 1021939592234, 13838041⟩,
    ⟨1022785, 1027898, 1021939592234, 1027061512594, 13843028⟩,
    ⟨1027898, 1033037, 1027061512594, 1032074494024, 13848015⟩,
    ⟨1033037, 1038202, 1032074494024, 1037227810768, 13853002⟩,
    ⟨1038202, 1043393, 1037227810768, 1042313693098, 13857990⟩,
    ⟨1043393, 1048576, 1042313693098, 1047498434528, 13862945⟩
  ]⟩,
  ⟨1048576, 2097152, [
    ⟨1048576, 1053818, 1047498434528, 1052615701436, 13867932⟩,
    ⟨1053818, 1059087, 1052615701436, 1057831918980, 13872919⟩,
    ⟨1059087, 1064382, 1057831918980, 1063022255824, 13877906⟩,
    ⟨1064382, 1069703, 1063022255824, 1068353286736, 13882893⟩,
    ⟨1069703, 1075051, 1068353286736, 1073644569016, 13887880⟩,
    ⟨1075051, 1080426, 1073644569016, 1079146144348, 13892867⟩,
    ⟨1080426, 1085828, 1079146144348, 1084496818523, 13897855⟩,
    ⟨1085828, 1091257, 1084496818523, 1089835509851, 13902842⟩,
    ⟨1091257, 1096713, 1089835509851, 1095537720151, 13907830⟩,
    ⟨1096713, 1102196, 1095537720151, 1100949805964, 13912817⟩,
    ⟨1102196, 1107706, 1100949805964, 1106558680573, 13917803⟩,
    ⟨1107706, 1113244, 1106558680573, 1112461943533, 13922790⟩,
    ⟨1113244, 1118810, 1112461943533, 1117907704731, 13927778⟩,
    ⟨1118810, 1124404, 1117907704731, 1123313617551, 13932765⟩,
    ⟨1124404, 1130026, 1123313617551, 1128986283022, 13937753⟩,
    ⟨1130026, 1135676, 1128986283022, 1134730691902, 13942740⟩,
    ⟨1135676, 1141354, 1134730691902, 1140365573610, 13947727⟩,
    ⟨1141354, 1147060, 1140365573610, 1145848990212, 13952714⟩,
    ⟨1147060, 1152795, 1145848990212, 1151599563024, 13957701⟩,
    ⟨1152795, 1158558, 1151599563024, 1157491817360, 13962688⟩,
    ⟨1158558, 1164350, 1157491817360, 1163553788310, 13967675⟩,
    ⟨1164350, 1170171, 1163553788310, 1169394361026, 13972662⟩,
    ⟨1170171, 1176021, 1169394361026, 1175153152414, 13977649⟩,
    ⟨1176021, 1181901, 1175153152414, 1181333477526, 13982636⟩,
    ⟨1181901, 1187810, 1181333477526, 1187306192547, 13987623⟩,
    ⟨1187810, 1193749, 1187306192547, 1193378985721, 13992611⟩,
    ⟨1193749, 1199717, 1193378985721, 1199271974479, 13997598⟩,
    ⟨1199717, 1205715, 1199271974479, 1204985029159, 14002585⟩,
    ⟨1205715, 1211743, 1204985029159, 1210896224543, 14007572⟩,
    ⟨1211743, 1217801, 1210896224543, 1217159838416, 14012559⟩,
    ⟨1217801, 1223890, 1217159838416, 1223075242828, 14017546⟩,
    ⟨1223890, 1230009, 1223075242828, 1229175045118, 14022534⟩,
    ⟨1230009, 1236159, 1229175045118, 1234968411291, 14027521⟩,
    ⟨1236159, 1242339, 1234968411291, 1241212877351, 14032508⟩,
    ⟨1242339, 1248550, 1241212877351, 1247543787596, 14037495⟩,
    ⟨1248550, 1254792, 1247543787596, 1253736522158, 14042482⟩,
    ⟨1254792, 1261065, 1253736522158, 1260142168022, 14047469⟩,
    ⟨1261065, 1267370, 1260142168022, 1266578192870, 14052456⟩,
    ⟨1267370, 1273706, 1266578192870, 1273072731536, 14057443⟩,
    ⟨1273706, 1280074, 1273072731536, 1279175826156, 14062430⟩,
    ⟨1280074, 1286474, 1279175826156, 1285590568308, 14067417⟩,
    ⟨1286474, 1292906, 1285590568308, 1292063874148, 14072404⟩,
    ⟨1292906, 1299370, 1292063874148, 1298426855332, 14077392⟩,
    ⟨1299370, 1305866, 1298426855332, 1304848419700, 14082378⟩,
    ⟨1305866, 1312395, 1304848419700, 1311469481720, 14087366⟩,
    ⟨1312395, 1318956, 1311469481720, 1317966056453, 14092353⟩,
    ⟨1318956, 1325550, 1317966056453, 1324620000933, 14097340⟩,
    ⟨1325550, 1332177, 1324620000933, 1331078866699, 14102327⟩,
    ⟨1332177, 1338837, 1331078866699, 1337751625748, 14107313⟩,
    ⟨1338837, 1345531, 1337751625748, 1344497305626, 14112301⟩,
    ⟨1345531, 1352258, 1344497305626, 1351061844546, 14117288⟩,
    ⟨1352258, 1359019, 1351061844546, 1357854658821, 14122275⟩,
    ⟨1359019, 1365814, 1357854658821, 1364607490535, 14127263⟩,
    ⟨1365814, 1372643, 1364607490535, 1371390970535, 14132250⟩,
    ⟨1372643, 1379506, 1371390970535, 1378487864011, 14137238⟩,
    ⟨1379506, 1386403, 1378487864011, 1385360985361, 14142225⟩,
    ⟨1386403, 1393335, 1385360985361, 1392095058273, 14147212⟩,
    ⟨1393335, 1400301, 1392095058273, 1399609875942, 14152199⟩,
    ⟨1400301, 1407302, 1399609875942, 1406263753362, 14157186⟩,
    ⟨1407302, 1414338, 1406263753362, 1413359002536, 14162174⟩,
    ⟨1414338, 1421409, 1413359002536, 1419989233884, 14167161⟩,
    ⟨1421409, 1428516, 1419989233884, 1427188685068, 14172148⟩,
    ⟨1428516, 1435658, 1427188685068, 1434716743753, 14177135⟩,
    ⟨1435658, 1442836, 1434716743753, 1441779441007, 14182123⟩,
    ⟨1442836, 1450050, 1441779441007, 1449014867107, 14187110⟩,
    ⟨1450050, 1457300, 1449014867107, 1456408949644, 14192097⟩,
    ⟨1457300, 1464586, 1456408949644, 1463720448419, 14197085⟩,
    ⟨1464586, 1471908, 1463720448419, 1470920898923, 14202072⟩,
    ⟨1471908, 1479267, 1470920898923, 1478365397839, 14207059⟩,
    ⟨1479267, 1486663, 1478365397839, 1485698813575, 14212046⟩,
    ⟨1486663, 1494096, 1485698813575, 1493432879527, 14217033⟩,
    ⟨1494096, 1501566, 1493432879527, 1500742998321, 14222021⟩,
    ⟨1501566, 1509073, 1500742998321, 1508610533745, 14227008⟩,
    ⟨1509073, 1516618, 1508610533745, 1516110795110, 14231995⟩,
    ⟨1516618, 1524201, 1516110795110, 1523570973678, 14236982⟩,
    ⟨1524201, 1531822, 1523570973678, 1530962556108, 14241970⟩,
    ⟨1531822, 1539481, 1530962556108, 1538541937232, 14246957⟩,
    ⟨1539481, 1547178, 1538541937232, 1546081216137, 14251945⟩,
    ⟨1547178, 1554913, 1546081216137, 1553851244077, 14256932⟩,
    ⟨1554913, 1562687, 1553851244077, 1561652513770, 14261919⟩,
    ⟨1562687, 1570500, 1561652513770, 1569413710634, 14266906⟩,
    ⟨1570500, 1578352, 1569413710634, 1577334611249, 14271893⟩,
    ⟨1578352, 1586243, 1577334611249, 1585015572689, 14276880⟩,
    ⟨1586243, 1594174, 1585015572689, 1592699217673, 14281868⟩,
    ⟨1594174, 1602144, 1592699217673, 1600771290748, 14286855⟩,
    ⟨1602144, 1610154, 1600771290748, 1608903348846, 14291842⟩,
    ⟨1610154, 1618204, 1608903348846, 1616809495283, 14296829⟩,
    ⟨1618204, 1626295, 1616809495283, 1625018737667, 14301816⟩,
    ⟨1626295, 1634426, 1625018737667, 1633402524811, 14306804⟩,
    ⟨1634426, 1642598, 1633402524811, 1641173827324, 14311791⟩,
    ⟨1642598, 1650810, 1641173827324, 1649506192120, 14316778⟩,
    ⟨1650810, 1659064, 1649506192120, 1657769851102, 14321766⟩,
    ⟨1659064, 1667359, 1657769851102, 1665993407324, 14326753⟩,
    ⟨1667359, 1675695, 1665993407324, 1674506460884, 14331740⟩,
    ⟨1675695, 1684073, 1674506460884, 1682764415636, 14336727⟩,
    ⟨1684073, 1692493, 1682764415636, 1691211685771, 14341715⟩,
    ⟨1692493, 1700955, 1691211685771, 1699819706971, 14346702⟩,
    ⟨1700955, 1709459, 1699819706971, 1708315906859, 14351689⟩,
    ⟨1709459, 1718006, 1708315906859, 1716657135615, 14356676⟩,
    ⟨1718006, 1726596, 1716657135615, 1725187964031, 14361664⟩,
    ⟨1726596, 1735228, 1725187964031, 1733678654772, 14366651⟩,
    ⟨1735228, 1743904, 1733678654772, 1742359124124, 14371638⟩,
    ⟨1743904, 1752623, 1742359124124, 1751387645252, 14376626⟩,
    ⟨1752623, 1761386, 1751387645252, 1759743362405, 14381613⟩,
    ⟨1761386, 1770192, 1759743362405, 1768504801805, 14386600⟩,
    ⟨1770192, 1779042, 1768504801805, 1777456368919, 14391587⟩,
    ⟨1779042, 1787937, 1777456368919, 1786411037947, 14396574⟩,
    ⟨1787937, 1796876, 1786411037947, 1795296801701, 14401562⟩,
    ⟨1796876, 1805860, 1795296801701, 1804315301375, 14406549⟩,
    ⟨1805860, 1814889, 1804315301375, 1813495449807, 14411536⟩,
    ⟨1814889, 1823963, 1813495449807, 1822448111211, 14416524⟩,
    ⟨1823963, 1833082, 1822448111211, 1831894200916, 14421511⟩,
    ⟨1833082, 1842247, 1831894200916, 1840622232206, 14426498⟩,
    ⟨1842247, 1851458, 1840622232206, 1849916108546, 14431485⟩,
    ⟨1851458, 1860715, 1849916108546, 1859516363091, 14436473⟩,
    ⟨1860715, 1870018, 1859516363091, 1868932195011, 14441460⟩,
    ⟨1870018, 1879368, 1868932195011, 1878279046867, 14446448⟩,
    ⟨1879368, 1888764, 1878279046867, 1887658028182, 14451435⟩,
    ⟨1888764, 1898207, 1887658028182, 1897257092390, 14456422⟩,
    ⟨1898207, 1907698, 1897257092390, 1906454548514, 14461409⟩,
    ⟨1907698, 1917236, 1906454548514, 1916335097665, 14466397⟩,
    ⟨1917236, 1926822, 1916335097665, 1925900682489, 14471384⟩,
    ⟨1926822, 1936456, 1925900682489, 1935570898985, 14476372⟩,
    ⟨1936456, 1946138, 1935570898985, 1945461667182, 14481359⟩,
    ⟨1946138, 1955868, 1945461667182, 1955182005348, 14486346⟩,
    ⟨1955868, 1965647, 1955182005348, 1964789759790, 14491334⟩,
    ⟨1965647, 1975475, 1964789759790, 1974052908909, 14496321⟩,
    ⟨1975475, 1985352, 1974052908909, 1984102315353, 14501308⟩,
    ⟨1985352, 1995278, 1984102315353, 1993995608543, 14506295⟩,
    ⟨1995278, 2005254, 1993995608543, 2004255085624, 14511283⟩,
    ⟨2005254, 2015280, 2004255085624, 2014547121054, 14516270⟩,
    ⟨2015280, 2025356, 2014547121054, 2024479661526, 14521258⟩,
    ⟨2025356, 2035482, 2024479661526, 2034909505436, 14526245⟩,
    ⟨2035482, 2045659, 2034909505436, 2044877930588, 14531232⟩,
    ⟨2045659, 2055887, 2044877930588, 2054878849260, 14536219⟩,
    ⟨2055887, 2066166, 2054878849260, 2065377600714, 14541207⟩,
    ⟨2066166, 2076496, 2065377600714, 2075574482708, 14546194⟩,
    ⟨2076496, 2086878, 2075574482708, 2085833065313, 14551181⟩,
    ⟨2086878, 2097152, 2085833065313, 2096022329713, 14556092⟩
  ]⟩,
  ⟨2097152, 3145728, [
    ⟨2097152, 2107637, 2096022329713, 2106637356304, 14561079⟩,
    ⟨2107637, 2118175, 2106637356304, 2117328849482, 14566067⟩,
    ⟨2118175, 2128765, 2117328849482, 2127776295200, 14571054⟩,
    ⟨2128765, 2139408, 2127776295200, 2138358500966, 14576041⟩,
    ⟨2139408, 2150105, 2138358500966, 2149119300368, 14581029⟩,
    ⟨2150105, 2160855, 2149119300368, 2160204672528, 14586016⟩,
    ⟨2160855, 2171659, 2160204672528, 2170797740706, 14591003⟩,
    ⟨2171659, 2182517, 2170797740706, 2181657158010, 14595991⟩,
    ⟨2182517, 2193429, 2181657158010, 2192622492488, 14600978⟩,
    ⟨2193429, 2204396, 2192622492488, 2203328665566, 14605966⟩,
    ⟨2204396, 2215417, 2203328665566, 2214330713175, 14610953⟩,
    ⟨2215417, 2226494, 2214330713175, 2225204972535, 14615940⟩,
    ⟨2226494, 2237626, 2225204972535, 2236594675447, 14620928⟩,
    ⟨2237626, 2248814, 2236594675447, 2247710370847, 14625915⟩,
    ⟨2248814, 2260058, 2247710370847, 2258946904351, 14630903⟩,
    ⟨2260058, 2271358, 2258946904351, 2270640980461, 14635890⟩,
    ⟨2271358, 2282714, 2270640980461, 2281899814874, 14640877⟩,
    ⟨2282714, 2294127, 2281899814874, 2293206421882, 14645864⟩,
    ⟨2294127, 2305597, 2293206421882, 2304575483034, 14650852⟩,
    ⟨2305597, 2317124, 2304575483034, 2316007037454, 14655839⟩,
    ⟨2317124, 2328709, 2316007037454, 2327471803386, 14660826⟩,
    ⟨2328709, 2340352, 2327471803386, 2338911137526, 14665813⟩,
    ⟨2340352, 2352053, 2338911137526, 2350427716311, 14670801⟩,
    ⟨2352053, 2363813, 2350427716311, 2362256401439, 14675788⟩,
    ⟨2363813, 2375632, 2362256401439, 2373956979911, 14680776⟩,
    ⟨2375632, 2387510, 2373956979911, 2386087420149, 14685763⟩,
    ⟨2387510, 2399447, 2386087420149, 2398075072149, 14690750⟩,
    ⟨2399447, 2411444, 2398075072149, 2409816966811, 14695738⟩,
    ⟨2411444, 2423501, 2409816966811, 2422092072186, 14700725⟩,
    ⟨2423501, 2435618, 2422092072186, 2434003699716, 14705713⟩,
    ⟨2435618, 2447796, 2434003699716, 2446051763016, 14710700⟩,
    ⟨2447796, 2460034, 2446051763016, 2458530665592, 14715687⟩,
    ⟨2460034, 2472334, 2458530665592, 2470748825842, 14720675⟩,
    ⟨2472334, 2484695, 2470748825842, 2482823868682, 14725662⟩,
    ⟨2484695, 2497118, 2482823868682, 2495330189683, 14730649⟩,
    ⟨2497118, 2509603, 2495330189683, 2507899688044, 14735637⟩,
    ⟨2509603, 2522151, 2507899688044, 2520267071580, 14740624⟩,
    ⟨2522151, 2534761, 2520267071580, 2533257954871, 14745611⟩,
    ⟨2534761, 2547434, 2533257954871, 2545604206234, 14750599⟩,
    ⟨2547434, 2560171, 2545604206234, 2558412054882, 14755586⟩,
    ⟨2560171, 2572971, 2558412054882, 2571283274538, 14760573⟩,
    ⟨2572971, 2585835, 2571283274538, 2584527982755, 14765561⟩,
    ⟨2585835, 2598764, 2584527982755, 2597481753351, 14770548⟩,
    ⟨2598764, 2611757, 2597481753351, 2610173937916, 14775535⟩,
    ⟨2611757, 2624815, 2610173937916, 2623343383018, 14780522⟩,
    ⟨2624815, 2637939, 2623343383018, 2636428559368, 14785510⟩,
    ⟨2637939, 2651128, 2636428559368, 2649799168656, 14790497⟩,
    ⟨2651128, 2664383, 2649799168656, 2663203878066, 14795485⟩,
    ⟨2664383, 2677704, 2663203878066, 2676228293426, 14800472⟩,
    ⟨2677704, 2691092, 2676228293426, 2689790093870, 14805459⟩,
    ⟨2691092, 2704547, 2689790093870, 2703178737054, 14810446⟩,
    ⟨2704547, 2718069, 2703178737054, 2717001536976, 14815434⟩,
    ⟨2718069, 2731659, 2717001536976, 2730325095455, 14820421⟩,
    ⟨2731659, 2745317, 2730325095455, 2743919995508, 14825409⟩,
    ⟨2745317, 2759043, 2743919995508, 2757356334284, 14830396⟩,
    ⟨2759043, 2772838, 2757356334284, 2771316429687, 14835383⟩,
    ⟨2772838, 2786702, 2771316429687, 2785251538056, 14840371⟩,
    ⟨2786702, 2800635, 2785251538056, 2799042875638, 14845358⟩,
    ⟨2800635, 2814638, 2799042875638, 2813581364372, 14850346⟩,
    ⟨2814638, 2828711, 2813581364372, 2827471100727, 14855333⟩,
    ⟨2828711, 2842854, 2827471100727, 2842197678838, 14860321⟩,
    ⟨2842854, 2857068, 2842197678838, 2856171068358, 14865308⟩,
    ⟨2857068, 2871353, 2856171068358, 2870372200083, 14870295⟩,
    ⟨2871353, 2885709, 2870372200083, 2884563220065, 14875283⟩,
    ⟨2885709, 2900137, 2884563220065, 2898892920075, 14880270⟩,
    ⟨2900137, 2914637, 2898892920075, 2913331619365, 14885257⟩,
    ⟨2914637, 2929210, 2913331619365, 2927864498485, 14890245⟩,
    ⟨2929210, 2943856, 2927864498485, 2942342663989, 14895232⟩,
    ⟨2943856, 2958575, 2942342663989, 2956840578049, 14900220⟩,
    ⟨2958575, 2973367, 2956840578049, 2971850121498, 14905207⟩,
    ⟨2973367, 2988233, 2971850121498, 2986834866468, 14910194⟩,
    ⟨2988233, 3003174, 2986834866468, 3001839539560, 14915182⟩,
    ⟨3003174, 3018189, 3001839539560, 3016819389236, 14920169⟩,
    ⟨3018189, 3033279, 3016819389236, 3031669919456, 14925156⟩,
    ⟨3033279, 3048445, 3031669919456, 3046674714176, 14930144⟩,
    ⟨3048445, 3063687, 3046674714176, 3061759196486, 14935131⟩,
    ⟨3063687, 3079005, 3061759196486, 3077386560960, 14940119⟩,
    ⟨3079005, 3094400, 3077386560960, 3092989251624, 14945106⟩,
    ⟨3094400, 3109872, 3092989251624, 3108357948256, 14950094⟩,
    ⟨3109872, 3125421, 3108357948256, 3123896277415, 14955081⟩,
    ⟨3125421, 3141048, 3123896277415, 3139409868968, 14960069⟩,
    ⟨3141048, 3145728, 3139409868968, 3144062913195, 14961557⟩
  ]⟩,
  ⟨3145728, 4194304, [
    ⟨3145728, 3161456, 3144062913195, 3159882551260, 14966545⟩,
    ⟨3161456, 3177263, 3159882551260, 3175827232840, 14971532⟩,
    ⟨3177263, 3193149, 3175827232840, 3191867085760, 14976520⟩,
    ⟨3193149, 3209114, 3191867085760, 3208271835925, 14981507⟩,
    ⟨3209114, 3225159, 3208271835925, 3224457249445, 14986494⟩,
    ⟨3225159, 3241284, 3224457249445, 3240737998897, 14991482⟩,
    ⟨3241284, 3257490, 3240737998897, 3256754227789, 14996469⟩,
    ⟨3257490, 3273777, 3256754227789, 3273030807549, 15001456⟩,
    ⟨3273777, 3290145, 3273030807549, 3289642941057, 15006444⟩,
    ⟨3290145, 3306595, 3289642941057, 3305810252244, 15011431⟩,
    ⟨3306595, 3323127, 3305810252244, 3322418410552, 15016418⟩,
    ⟨3323127, 3339742, 3322418410552, 3338836807310, 15021406⟩,
    ⟨3339742, 3356440, 3338836807310, 3355395892396, 15026393⟩,
    ⟨3356440, 3373222, 3355395892396, 3372140849716, 15031380⟩,
    ⟨3373222, 3390088, 3372140849716, 3389146981924, 15036368⟩,
    ⟨3390088, 3407038, 3389146981924, 3406143713074, 15041355⟩,
    ⟨3407038, 3424073, 3406143713074, 3423251405065, 15046343⟩,
    ⟨3424073, 3441193, 3423251405065, 3440771153185, 15051330⟩,
    ⟨3441193, 3458398, 3440771153185, 3457950412023, 15056318⟩,
    ⟨3458398, 3475689, 3457950412023, 3474743767098, 15061305⟩,
    ⟨3475689, 3493067, 3474743767098, 3491648146722, 15066292⟩,
    ⟨3493067, 3510532, 3491648146722, 3508754049522, 15071280⟩,
    ⟨3510532, 3528084, 3508754049522, 3525956070169, 15076267⟩,
    ⟨3528084, 3545724, 3525956070169, 3543405081047, 15081254⟩,
    ⟨3545724, 3563452, 3543405081047, 3561101242913, 15086242⟩,
    ⟨3563452, 3581269, 3561101242913, 3578848528217, 15091229⟩,
    ⟨3581269, 3599175, 3578848528217, 3596933796183, 15096217⟩,
    ⟨3599175, 3617170, 3596933796183, 3615478074695, 15101204⟩,
    ⟨3617170, 3635255, 3615478074695, 3633892521524, 15106191⟩,
    ⟨3635255, 3653431, 3633892521524, 3651330822090, 15111179⟩,
    ⟨3653431, 3671698, 3651330822090, 3669696963780, 15116166⟩,
    ⟨3671698, 3690056, 3669696963780, 3688265740892, 15121154⟩,
    ⟨3690056, 3708506, 3688265740892, 3706961651168, 15126141⟩,
    ⟨3708506, 3727048, 3706961651168, 3725875562418, 15131129⟩,
    ⟨3727048, 3745683, 3725875562418, 3744356760054, 15136116⟩,
    ⟨3745683, 3764411, 3744356760054, 3762874329023, 15141103⟩,
    ⟨3764411, 3783233, 3762874329023, 3781549459226, 15146091⟩,
    ⟨3783233, 3802149, 3781549459226, 3800427702414, 15151078⟩,
    ⟨3802149, 3821159, 3800427702414, 3819781998696, 15156066⟩,
    ⟨3821159, 3840264, 3819781998696, 3838915247582, 15161053⟩,
    ⟨3840264, 3859465, 3838915247582, 3858267115898, 15166041⟩,
    ⟨3859465, 3878762, 3858267115898, 3877139874730, 15171028⟩,
    ⟨3878762, 3898155, 3877139874730, 3896883870245, 15176015⟩,
    ⟨3898155, 3917645, 3896883870245, 3916178925058, 15181003⟩,
    ⟨3917645, 3937233, 3916178925058, 3935920712058, 15185990⟩,
    ⟨3937233, 3956919, 3935920712058, 3955744938348, 15190978⟩,
    ⟨3956919, 3976703, 3955744938348, 3975332537233, 15195965⟩,
    ⟨3976703, 3996586, 3975332537233, 3994835359932, 15200953⟩,
    ⟨3996586, 4016568, 3994835359932, 4014785553212, 15205940⟩,
    ⟨4016568, 4036650, 4014785553212, 4035107351684, 15210927⟩,
    ⟨4036650, 4056833, 4035107351684, 4055405382294, 15215915⟩,
    ⟨4056833, 4077117, 4055405382294, 4075801390974, 15220902⟩,
    ⟨4077117, 4097502, 4075801390974, 4096402020144, 15225890⟩,
    ⟨4097502, 4117989, 4096402020144, 4116780933570, 15230877⟩,
    ⟨4117989, 4138578, 4116780933570, 4136572320906, 15235864⟩,
    ⟨4138578, 4159270, 4136572320906, 4157528492406, 15240852⟩,
    ⟨4159270, 4180066, 4157528492406, 4178445783514, 15245839⟩,
    ⟨4180066, 4194304, 4178445783514, 4192963059042, 15249239⟩
  ]⟩,
  ⟨4194304, 5242880, [
    ⟨4194304, 4215275, 4192963059042, 4214013892302, 15254227⟩,
    ⟨4215275, 4236351, 4214013892302, 4234964793124, 15259214⟩,
    ⟨4236351, 4257532, 4234964793124, 4256105712894, 15264202⟩,
    ⟨4257532, 4278819, 4256105712894, 4277116116958, 15269189⟩,
    ⟨4278819, 4300213, 4277116116958, 4298163932864, 15274177⟩,
    ⟨4300213, 4321714, 4298163932864, 4319738112432, 15279164⟩,
    ⟨4321714, 4343322, 4319738112432, 4341258198448, 15284152⟩,
    ⟨4343322, 4365038, 4341258198448, 4362632414770, 15289139⟩,
    ⟨4365038, 4386863, 4362632414770, 4384610073832, 15294126⟩,
    ⟨4386863, 4408797, 4384610073832, 4406120628116, 15299114⟩,
    ⟨4408797, 4430840, 4406120628116, 4428923738606, 15304101⟩,
    ⟨4430840, 4452994, 4428923738606, 4451397481258, 15309089⟩,
    ⟨4452994, 4475258, 4451397481258, 4473771346294, 15314076⟩,
    ⟨4475258, 4497634, 4473771346294, 4496428241950, 15319064⟩,
    ⟨4497634, 4520122, 4496428241950, 4518648115900, 15324051⟩,
    ⟨4520122, 4542722, 4518648115900, 4540783246772, 15329038⟩,
    ⟨4542722, 4565435, 4540783246772, 4563784285772, 15334026⟩,
    ⟨4565435, 4588262, 4563784285772, 4586547381064, 15339013⟩,
    ⟨4588262, 4611203, 4586547381064, 4609762854577, 15344001⟩,
    ⟨4611203, 4634259, 4609762854577, 4632586799733, 15348988⟩,
    ⟨4634259, 4657430, 4632586799733, 4655372100117, 15353976⟩,
    ⟨4657430, 4680717, 4655372100117, 4678917390396, 15358963⟩,
    ⟨4680717, 4704120, 4678917390396, 4702670058642, 15363951⟩,
    ⟨4704120, 4727640, 4702670058642, 4726092320154, 15368938⟩,
    ⟨4727640, 4751278, 4726092320154, 4749798914046, 15373926⟩,
    ⟨4751278, 4775034, 4749798914046, 4773220998545, 15378913⟩,
    ⟨4775034, 4798909, 4773220998545, 4796881438283, 15383901⟩,
    ⟨4798909, 4822903, 4796881438283, 4821118936883, 15388888⟩,
    ⟨4822903, 4847017, 4821118936883, 4845025626311, 15393876⟩,
    ⟨4847017, 4871252, 4845025626311, 4869540616207, 15398863⟩,
    ⟨4871252, 4895608, 4869540616207, 4894325412466, 15403851⟩,
    ⟨4895608, 4920086, 4894325412466, 4918779238372, 15408838⟩,
    ⟨4920086, 4944686, 4918779238372, 4943595498232, 15413826⟩,
    ⟨4944686, 4969409, 4943595498232, 4968728163422, 15418813⟩,
    ⟨4969409, 4994256, 4968728163422, 4993899806654, 15423801⟩,
    ⟨4994256, 5019227, 4993899806654, 5018400721998, 15428788⟩,
    ⟨5019227, 5044323, 5018400721998, 5043480607998, 15433776⟩,
    ⟨5044323, 5069544, 5043480607998, 5068522281584, 15438763⟩,
    ⟨5069544, 5094891, 5068522281584, 5094050800334, 15443750⟩,
    ⟨5094891, 5120365, 5094050800334, 5119185897060, 15448738⟩,
    ⟨5120365, 5145966, 5119185897060, 5145132701335, 15453725⟩,
    ⟨5145966, 5171695, 5145132701335, 5170685953924, 15458713⟩,
    ⟨5171695, 5197553, 5170685953924, 5196123740424, 15463700⟩,
    ⟨5197553, 5223540, 5196123740424, 5222374102263, 15468687⟩,
    ⟨5223540, 5242880, 5222374102263, 5241745525779, 15472383⟩
  ]⟩
]

theorem rangeChecked02 : checkGroups rangeGroups02 = true := by decide +kernel

def rangeGroups03 : List Group := [
  ⟨5242880, 6291456, [
    ⟨5242880, 5269094, 5241745525779, 5268258260589, 15477370⟩,
    ⟨5269094, 5295439, 5268258260589, 5294609233905, 15482358⟩,
    ⟨5295439, 5321916, 5294609233905, 5320829308990, 15487345⟩,
    ⟨5321916, 5348525, 5320829308990, 5347770476077, 15492333⟩,
    ⟨5348525, 5375267, 5347770476077, 5374239898637, 15497320⟩,
    ⟨5375267, 5402143, 5374239898637, 5401368937637, 15502308⟩,
    ⟨5402143, 5429153, 5401368937637, 5428367138232, 15507295⟩,
    ⟨5429153, 5456298, 5428367138232, 5455342998369, 15512283⟩,
    ⟨5456298, 5483579, 5455342998369, 5482622359029, 15517270⟩,
    ⟨5483579, 5510996, 5482622359029, 5509972575863, 15522257⟩,
    ⟨5510996, 5538550, 5509972575863, 5537455799513, 15527245⟩,
    ⟨5538550, 5566242, 5537455799513, 5564528479889, 15532232⟩,
    ⟨5566242, 5594073, 5564528479889, 5592573161989, 15537220⟩,
    ⟨5594073, 5622043, 5592573161989, 5620176121621, 15542207⟩,
    ⟨5622043, 5650153, 5620176121621, 5648083336646, 15547195⟩,
    ⟨5650153, 5678403, 5648083336646, 5676155025156, 15552182⟩,
    ⟨5678403, 5706795, 5676155025156, 5704966903996, 15557170⟩,
    ⟨5706795, 5735328, 5704966903996, 5733414526992, 15562157⟩,
    ⟨5735328, 5764004, 5733414526992, 5762011370520, 15567144⟩,
    ⟨5764004, 5792824, 5762011370520, 5790414939288, 15572132⟩,
    ⟨5792824, 5821788, 5790414939288, 5819419534866, 15577119⟩,
    ⟨5821788, 5850896, 5819419534866, 5848402253886, 15582107⟩,
    ⟨5850896, 5880150, 5848402253886, 5877441010008, 15587094⟩,
    ⟨5880150, 5909550, 5877441010008, 5907455767858, 15592082⟩,
    ⟨5909550, 5939097, 5907455767858, 5937682887580, 15597069⟩,
    ⟨5939097, 5968792, 5937682887580, 5967061560911, 15602057⟩,
    ⟨5968792, 5998635, 5967061560911, 5996527659983, 15607044⟩,
    ⟨5998635, 6028628, 5996527659983, 6027392647247, 15612032⟩,
    ⟨6028628, 6058771, 6027392647247, 6056908813157, 15617019⟩,
    ⟨6058771, 6089064, 6056908813157, 6086934308689, 15622006⟩,
    ⟨6089064, 6119509, 6086934308689, 6117610097911, 15626994⟩,
    ⟨6119509, 6150106, 6117610097911, 6148139356804, 15631981⟩,
    ⟨6150106, 6180856, 6148139356804, 6179069281486, 15636969⟩,
    ⟨6180856, 6211760, 6179069281486, 6209711873290, 15641956⟩,
    ⟨6211760, 6242818, 6209711873290, 6240458118250, 15646944⟩,
    ⟨6242818, 6274032, 6240458118250, 6271965455353, 15651931⟩,
    ⟨6274032, 6291456, 6271965455353, 6289623962593, 15654705⟩
  ]⟩,
  ⟨6291456, 7340032, [
    ⟨6291456, 6322913, 6289623962593, 6321554074581, 15659692⟩,
    ⟨6322913, 6354527, 6321554074581, 6353118404781, 15664680⟩,
    ⟨6354527, 6386299, 6353118404781, 6384191354442, 15669667⟩,
    ⟨6386299, 6418230, 6384191354442, 6415916854138, 15674654⟩,
    ⟨6418230, 6450321, 6415916854138, 6447668129188, 15679642⟩,
    ⟨6450321, 6482572, 6447668129188, 6479994149557, 15684629⟩,
    ⟨6482572, 6514984, 6479994149557, 6512487346364, 15689617⟩,
    ⟨6514984, 6547558, 6512487346364, 6545210595704, 15694604⟩,
    ⟨6547558, 6580295, 6545210595704, 6577881446656, 15699592⟩,
    ⟨6580295, 6613196, 6577881446656, 6611363609084, 15704579⟩,
    ⟨6613196, 6646261, 6611363609084, 6644165182892, 15709566⟩,
    ⟨6646261, 6679492, 6644165182892, 6677040029860, 15714554⟩,
    ⟨6679492, 6712889, 6677040029860, 6710585530354, 15719541⟩,
    ⟨6712889, 6746453, 6710585530354, 6744283196001, 15724529⟩,
    ⟨6746453, 6780185, 6744283196001, 6778196032497, 15729516⟩,
    ⟨6780185, 6814085, 6778196032497, 6811962278081, 15734504⟩,
    ⟨6814085, 6848155, 6811962278081, 6846132713042, 15739491⟩,
    ⟨6848155, 6882395, 6846132713042, 6880896522674, 15744479⟩,
    ⟨6882395, 6916806, 6880896522674, 6915261857486, 15749466⟩,
    ⟨6916806, 6951390, 6915261857486, 6950284008728, 15754454⟩,
    ⟨6951390, 6986146, 6950284008728, 6984875981723, 15759441⟩,
    ⟨6986146, 7021076, 6984875981723, 7019967600677, 15764429⟩,
    ⟨7021076, 7056181, 7019967600677, 7055716866749, 15769416⟩,
    ⟨7056181, 7091461, 7055716866749, 7090972657454, 15774403⟩,
    ⟨7091461, 7126918, 7090972657454, 7126318493294, 15779391⟩,
    ⟨7126918, 7162552, 7126318493294, 7161470303100, 15784378⟩,
    ⟨7162552, 7198364, 7161470303100, 7197170059626, 15789366⟩,
    ⟨7198364, 7234355, 7197170059626, 7233118007054, 15794353⟩,
    ⟨7234355, 7270526, 7233118007054, 7269424892672, 15799341⟩,
    ⟨7270526, 7306878, 7269424892672, 7305917086024, 15804328⟩,
    ⟨7306878, 7340032, 7305917086024, 7338831122134, 15808855⟩
  ]⟩,
  ⟨7340032, 8388608, [
    ⟨7340032, 7376732, 7338831122134, 7375788073225, 15813843⟩,
    ⟨7376732, 7413615, 7375788073225, 7412187201055, 15818830⟩,
    ⟨7413615, 7450683, 7412187201055, 7449752944987, 15823818⟩,
    ⟨7450683, 7487936, 7449752944987, 7486729033467, 15828805⟩,
    ⟨7487936, 7525375, 7486729033467, 7523479267020, 15833793⟩,
    ⟨7525375, 7563001, 7523479267020, 7561524016580, 15838780⟩,
    ⟨7563001, 7600816, 7561524016580, 7599121278044, 15843768⟩,
    ⟨7600816, 7638820, 7599121278044, 7637174138799, 15848755⟩,
    ⟨7638820, 7677014, 7637174138799, 7675556050602, 15853743⟩,
    ⟨7677014, 7715399, 7675556050602, 7713965894662, 15858730⟩,
    ⟨7715399, 7753975, 7713965894662, 7752324364786, 15863718⟩,
    ⟨7753975, 7792744, 7752324364786, 7790440994196, 15868705⟩,
    ⟨7792744, 7831707, 7790440994196, 7829712510678, 15873693⟩,
    ⟨7831707, 7870865, 7829712510678, 7869234545198, 15878680⟩,
    ⟨7870865, 7910219, 7869234545198, 7908911947862, 15883668⟩,
    ⟨7910219, 7949770, 7908911947862, 7948554142087, 15888655⟩,
    ⟨7949770, 7989518, 7948554142087, 7988272353445, 15893642⟩,
    ⟨7989518, 8029465, 7988272353445, 8027700955845, 15898630⟩,
    ⟨8029465, 8069612, 8027700955845, 8068000721323, 15903617⟩,
    ⟨8069612, 8109960, 8068000721323, 8107549513353, 15908605⟩,
    ⟨8109960, 8150509, 8107549513353, 8148113259361, 15913592⟩,
    ⟨8150509, 8191261, 8148113259361, 8189215032921, 15918580⟩,
    ⟨8191261, 8232217, 8189215032921, 8230265988647, 15923567⟩,
    ⟨8232217, 8273378, 8230265988647, 8271218303552, 15928555⟩,
    ⟨8273378, 8314744, 8271218303552, 8312932316508, 15933542⟩,
    ⟨8314744, 8356317, 8312932316508, 8354675326578, 15938530⟩,
    ⟨8356317, 8388608, 8354675326578, 8386655754900, 15942387⟩
  ]⟩,
  ⟨8388608, 9437184, [
    ⟨8388608, 8430551, 8386655754900, 8428358137910, 15947374⟩,
    ⟨8430551, 8472703, 8428358137910, 8469882136196, 15952362⟩,
    ⟨8472703, 8515066, 8469882136196, 8512887191751, 15957349⟩,
    ⟨8515066, 8557641, 8512887191751, 8555969539314, 15962337⟩,
    ⟨8557641, 8600429, 8555969539314, 8598905673550, 15967324⟩,
    ⟨8600429, 8643431, 8598905673550, 8642110777510, 15972312⟩,
    ⟨8643431, 8686648, 8642110777510, 8685361325903, 15977299⟩,
    ⟨8686648, 8730081, 8685361325903, 8729168774570, 15982287⟩,
    ⟨8730081, 8773731, 8729168774570, 8773101803522, 15987274⟩,
    ⟨8773731, 8817599, 8773101803522, 8816872624616, 15992262⟩,
    ⟨8817599, 8861686, 8816872624616, 8860417136394, 15997249⟩,
    ⟨8861686, 8905994, 8860417136394, 8904279268011, 16002237⟩,
    ⟨8905994, 8950523, 8904279268011, 8949435646915, 16007224⟩,
    ⟨8950523, 8995275, 8949435646915, 8994253825504, 16012211⟩,
    ⟨8995275, 9040251, 8994253825504, 9038381208749, 16017199⟩,
    ⟨9040251, 9085452, 9038381208749, 9083547753902, 16022187⟩,
    ⟨9085452, 9130879, 9083547753902, 9128600140016, 16027174⟩,
    ⟨9130879, 9176533, 9128600140016, 9174452123336, 16032162⟩,
    ⟨9176533, 9222415, 9174452123336, 9220767409648, 16037149⟩,
    ⟨9222415, 9268527, 9220767409648, 9267065017030, 16042137⟩,
    ⟨9268527, 9314869, 9267065017030, 9313697959374, 16047124⟩,
    ⟨9314869, 9361443, 9313697959374, 9360265136286, 16052112⟩,
    ⟨9361443, 9408250, 9360265136286, 9406894951782, 16057099⟩,
    ⟨9408250, 9437184, 9406894951782, 9435337512852, 16060170⟩
  ]⟩,
  ⟨9437184, 10485760, [
    ⟨9437184, 9484369, 9435337512852, 9482135315193, 16065157⟩,
    ⟨9484369, 9531790, 9482135315193, 9529783295118, 16070145⟩,
    ⟨9531790, 9579448, 9529783295118, 9577558587422, 16075132⟩,
    ⟨9579448, 9627345, 9577558587422, 9625943668502, 16080120⟩,
    ⟨9627345, 9675481, 9625943668502, 9674182904395, 16085107⟩,
    ⟨9675481, 9723858, 9674182904395, 9722227928065, 16090095⟩,
    ⟨9723858, 9772477, 9722227928065, 9770770695377, 16095082⟩,
    ⟨9772477, 9821339, 9770770695377, 9820053009647, 16100070⟩,
    ⟨9821339, 9870445, 9820053009647, 9868497021103, 16105057⟩,
    ⟨9870445, 9919797, 9868497021103, 9917487667948, 16110045⟩,
    ⟨9919797, 9969395, 9917487667948, 9966864125996, 16115032⟩,
    ⟨9969395, 10019241, 9966864125996, 10016014063927, 16120019⟩,
    ⟨10019241, 10069337, 10016014063927, 10066630460900, 16125007⟩,
    ⟨10069337, 10119683, 10066630460900, 10116956042180, 16129994⟩,
    ⟨10119683, 10170281, 10116956042180, 10167716695552, 16134982⟩,
    ⟨10170281, 10221132, 10167716695552, 10217508499917, 16139969⟩,
    ⟨10221132, 10272237, 10217508499917, 10269349956844, 16144957⟩,
    ⟨10272237, 10323598, 10269349956844, 10320335330052, 16149944⟩,
    ⟨10323598, 10375215, 10320335330052, 10372176506840, 16154932⟩,
    ⟨10375215, 10427091, 10372176506840, 10424324565453, 16159919⟩,
    ⟨10427091, 10479226, 10424324565453, 10476876678110, 16164907⟩,
    ⟨10479226, 10485760, 10476876678110, 10483375221170, 16165530⟩
  ]⟩,
  ⟨10485760, 11534336, [
    ⟨10485760, 10538188, 10483375221170, 10535751528972, 16170518⟩,
    ⟨10538188, 10590878, 10535751528972, 10588677781332, 16175505⟩,
    ⟨10590878, 10643832, 10588677781332, 10641555632456, 16180493⟩,
    ⟨10643832, 10697051, 10641555632456, 10695453280856, 16185480⟩,
    ⟨10697051, 10750536, 10695453280856, 10749140872744, 16190468⟩,
    ⟨10750536, 10804288, 10749140872744, 10802294356054, 16195455⟩,
    ⟨10804288, 10858309, 10802294356054, 10856322833459, 16200443⟩,
    ⟨10858309, 10912600, 10856322833459, 10910789283689, 16205430⟩,
    ⟨10912600, 10967163, 10910789283689, 10965758811127, 16210418⟩,
    ⟨10967163, 11021998, 10965758811127, 11020015556257, 16215405⟩,
    ⟨11021998, 11077107, 11020015556257, 11075554181889, 16220393⟩,
    ⟨11077107, 11132492, 11075554181889, 11130769150029, 16225380⟩,
    ⟨11132492, 11188154, 11130769150029, 11186958684045, 16230368⟩,
    ⟨11188154, 11244094, 11186958684045, 11242613480985, 16235355⟩,
    ⟨11244094, 11300314, 11242613480985, 11298512741591, 16240343⟩,
    ⟨11300314, 11356815, 11298512741591, 11354932772681, 16245330⟩,
    ⟨11356815, 11413599, 11354932772681, 11411256374869, 16250318⟩,
    ⟨11413599, 11470666, 11411256374869, 11468735133349, 16255305⟩,
    ⟨11470666, 11528019, 11468735133349, 11525922583830, 16260293⟩,
    ⟨11528019, 11534336, 11525922583830, 11532329354790, 16260840⟩
  ]⟩,
  ⟨11534336, 12582912, [
    ⟨11534336, 11592007, 11532329354790, 11590626082342, 16265828⟩,
    ⟨11592007, 11649967, 11590626082342, 11648664079447, 16270815⟩,
    ⟨11649967, 11708216, 11648664079447, 11706980281596, 16275803⟩,
    ⟨11708216, 11766757, 11706980281596, 11765037578736, 16280790⟩,
    ⟨11766757, 11825590, 11765037578736, 11824415525324, 16285778⟩,
    ⟨11825590, 11884717, 11824415525324, 11883436966919, 16290765⟩,
    ⟨11884717, 11944140, 11883436966919, 11943046831393, 16295753⟩,
    ⟨11944140, 12003860, 11943046831393, 12002691239053, 16300740⟩,
    ⟨12003860, 12063879, 12002691239053, 12063071349837, 16305728⟩,
    ⟨12063879, 12124198, 12063071349837, 12122866431027, 16310715⟩,
    ⟨12124198, 12184818, 12122866431027, 12183381373454, 16315703⟩,
    ⟨12184818, 12245742, 12183381373454, 12244437074744, 16320690⟩,
    ⟨12245742, 12306970, 12244437074744, 12305837949702, 16325678⟩,
    ⟨12306970, 12368504, 12305837949702, 12368188428672, 16330665⟩,
    ⟨12368504, 12430346, 12368188428672, 12430247574419, 16335653⟩,
    ⟨12430346, 12492497, 12430247574419, 12492194940659, 16340640⟩,
    ⟨12492497, 12554959, 12492194940659, 12554144870779, 16345628⟩,
    ⟨12554959, 12582912, 12554144870779, 12581674653547, 16347852⟩
  ]⟩,
  ⟨12582912, 13631488, [
    ⟨12582912, 12645826, 12581674653547, 12644878376282, 16352839⟩,
    ⟨12645826, 12709055, 12644878376282, 12707937799367, 16357827⟩,
    ⟨12709055, 12772600, 12707937799367, 12772603640295, 16362814⟩,
    ⟨12772600, 12836463, 12772603640295, 12836601746115, 16367802⟩,
    ⟨12836463, 12900645, 12836601746115, 12900488368793, 16372789⟩,
    ⟨12900645, 12965148, 12900488368793, 12964214299100, 16377777⟩,
    ⟨12965148, 13029973, 12964214299100, 13029073661776, 16382764⟩,
    ⟨13029973, 13095122, 13029073661776, 13092903955816, 16387752⟩,
    ⟨13095122, 13160597, 13092903955816, 13158491304555, 16392739⟩,
    ⟨13160597, 13226399, 13158491304555, 13224688928454, 16397727⟩,
    ⟨13226399, 13292530, 13224688928454, 13290250576312, 16402714⟩,
    ⟨13292530, 13358992, 13290250576312, 13356980700346, 16407702⟩,
    ⟨13358992, 13425786, 13356980700346, 13423747519198, 16412689⟩,
    ⟨13425786, 13492914, 13423747519198, 13490468958526, 16417677⟩,
    ⟨13492914, 13560378, 13490468958526, 13557440582318, 16422664⟩,
    ⟨13560378, 13628179, 13557440582318, 13625500344554, 16427652⟩,
    ⟨13628179, 13631488, 13625500344554, 13628933774400, 16427894⟩
  ]⟩
]

theorem rangeChecked03 : checkGroups rangeGroups03 = true := by decide +kernel

def rangeGroups : List Group :=
  rangeGroups00 ++ rangeGroups01 ++ rangeGroups02 ++ rangeGroups03

theorem range_checked : checkGroups rangeGroups = true := by
  simp only [rangeGroups, checkGroups_append, rangeChecked00, rangeChecked01, rangeChecked02, rangeChecked03, Bool.and_self]

theorem range_linked : linked 1 0 13631488 13628933774400
    (rangeGroups.flatMap Group.blocks) = true := by decide +kernel

theorem range_sound (hTheta : Chebyshev.theta (1 : ℝ) ≤ (0 : ℝ) / 1000000) :
    Chebyshev.theta (13631488 : ℝ) ≤ (13628933774400 : ℝ) / 1000000 ∧
      ∀ n : ℕ, 1000 < n → 1 < n → n ≤ 13631488 →
        Chebyshev.psi (n : ℝ) < 1.03883 * (n : ℝ) := by
  simpa only [scale, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    (linked_sound (rangeGroups.flatMap Group.blocks) 1 0 13631488 13628933774400
      (checkGroups_sound rangeGroups range_checked) range_linked
      (by simpa only [scale, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using hTheta))

end OddGoldbachPsi

theorem solution :
    Chebyshev.theta (13631488 : ℝ) ≤ (13628933774400 : ℝ) / 1000000 ∧
    ∀ n : ℕ, 1000 < n → n ≤ 13631488 →
      Chebyshev.psi (n : ℝ) < 1.03883 * (n : ℝ) := by
  have hStart : Chebyshev.theta (1 : ℝ) ≤ (0 : ℝ) / 1000000 := by
    rw [Chebyshev.theta_eq_zero_of_lt_two (by norm_num)]
    norm_num
  obtain ⟨hTheta, hPsi⟩ := OddGoldbachPsi.range_sound hStart
  exact ⟨hTheta, fun n hn hN => hPsi n hn (by omega) hN⟩

#print axioms solution
