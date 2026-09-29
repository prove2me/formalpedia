-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_high_cert205
-- status  : ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-09-27T18:22:40.714984+00:00
-- url     : https://prove2.me/submissions/fd2b2456-d465-4561-84e1-9aa706ca2dd7

-- shard 5: independent (no imports); the tight base bound is a hypothesis
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
import Mathlib.Data.Nat.Size


namespace TFPS1

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

namespace TFPS1
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

def divisors : List Nat := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999, 2003, 2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143, 2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647, 2657, 2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731, 2741, 2749, 2753, 2767, 2777, 2789, 2791, 2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861, 2879, 2887, 2897, 2903, 2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971, 2999, 3001, 3011, 3019, 3023, 3037, 3041, 3049, 3061, 3067, 3079, 3083, 3089, 3109, 3119, 3121, 3137, 3163, 3167, 3169, 3181, 3187, 3191, 3203, 3209, 3217, 3221, 3229, 3251, 3253, 3257, 3259, 3271, 3299, 3301, 3307, 3313, 3319, 3323, 3329, 3331, 3343, 3347, 3359, 3361, 3371, 3373, 3389, 3391, 3407, 3413, 3433, 3449, 3457, 3461, 3463, 3467, 3469, 3491, 3499, 3511, 3517, 3527, 3529, 3533, 3539, 3541, 3547, 3557, 3559, 3571, 3581, 3583, 3593, 3607, 3613, 3617, 3623, 3631, 3637, 3643, 3659, 3671, 3673, 3677, 3691, 3697, 3701, 3709, 3719, 3727, 3733, 3739, 3761, 3767, 3769, 3779, 3793, 3797, 3803, 3821, 3823, 3833, 3847, 3851, 3853, 3863, 3877, 3881, 3889, 3907, 3911, 3917, 3919, 3923, 3929, 3931, 3943, 3947, 3967, 3989, 4001, 4003, 4007, 4013, 4019, 4021, 4027, 4049, 4051, 4057, 4073, 4079, 4091, 4093, 4099, 4111, 4127, 4129, 4133, 4139, 4153, 4157, 4159, 4177, 4201, 4211, 4217, 4219, 4229, 4231, 4241, 4243, 4253, 4259, 4261, 4271, 4273, 4283, 4289, 4297, 4327, 4337, 4339, 4349, 4357, 4363, 4373, 4391, 4397, 4409, 4421, 4423, 4441, 4447, 4451, 4457, 4463, 4481, 4483, 4493, 4507, 4513, 4517, 4519, 4523, 4547, 4549, 4561, 4567, 4583, 4591, 4597, 4603, 4621, 4637, 4639, 4643, 4649, 4651, 4657, 4663, 4673, 4679, 4691, 4703, 4721, 4723, 4729, 4733, 4751, 4759, 4783, 4787, 4789, 4793, 4799, 4801, 4813, 4817, 4831, 4861, 4871, 4877, 4889, 4903, 4909, 4919, 4931, 4933, 4937, 4943, 4951, 4957, 4967, 4969, 4973, 4987, 4993, 4999, 5003, 5009, 5011, 5021, 5023, 5039, 5051, 5059, 5077, 5081, 5087, 5099, 5101, 5107, 5113, 5119, 5147, 5153, 5167, 5171, 5179, 5189, 5197, 5209, 5227, 5231, 5233, 5237, 5261, 5273, 5279, 5281, 5297, 5303, 5309, 5323, 5333, 5347, 5351, 5381, 5387, 5393, 5399, 5407, 5413, 5417, 5419, 5431, 5437, 5441, 5443, 5449, 5471, 5477, 5479, 5483, 5501, 5503, 5507, 5519, 5521, 5527, 5531, 5557, 5563, 5569, 5573, 5581, 5591, 5623, 5639, 5641, 5647, 5651, 5653, 5657, 5659, 5669, 5683, 5689, 5693, 5701, 5711, 5717, 5737, 5741, 5743, 5749, 5779, 5783, 5791, 5801, 5807, 5813, 5821, 5827, 5839, 5843, 5849, 5851, 5857, 5861, 5867, 5869, 5879, 5881, 5897, 5903, 5923, 5927, 5939, 5953, 5981, 5987, 6007, 6011, 6029, 6037, 6043, 6047, 6053, 6067, 6073, 6079, 6089, 6091, 6101, 6113, 6121, 6131, 6133, 6143, 6151, 6163, 6173, 6197, 6199, 6203, 6211, 6217, 6221, 6229, 6247, 6257, 6263, 6269, 6271, 6277, 6287, 6299, 6301, 6311, 6317, 6323, 6329, 6337, 6343, 6353, 6359, 6361, 6367, 6373, 6379, 6389, 6397, 6421, 6427, 6449, 6451, 6469, 6473, 6481, 6491, 6521, 6529, 6547, 6551, 6553, 6563, 6569, 6571, 6577, 6581, 6599, 6607, 6619, 6637, 6653, 6659, 6661, 6673, 6679, 6689, 6691, 6701, 6703, 6709, 6719, 6733, 6737, 6761, 6763, 6779, 6781, 6791, 6793, 6803, 6823, 6827, 6829, 6833, 6841, 6857, 6863, 6869, 6871, 6883, 6899, 6907, 6911, 6917, 6947, 6949, 6959, 6961, 6967, 6971, 6977, 6983, 6991, 6997, 7001, 7013, 7019, 7027, 7039, 7043, 7057, 7069, 7079, 7103, 7109, 7121, 7127, 7129, 7151, 7159, 7177, 7187, 7193, 7207, 7211, 7213, 7219, 7229, 7237, 7243, 7247, 7253, 7283, 7297, 7307, 7309, 7321, 7331, 7333, 7349, 7351, 7369, 7393, 7411, 7417, 7433, 7451, 7457, 7459, 7477, 7481, 7487, 7489, 7499, 7507, 7517, 7523, 7529, 7537, 7541, 7547, 7549, 7559, 7561, 7573, 7577, 7583, 7589, 7591, 7603, 7607, 7621, 7639, 7643, 7649, 7669, 7673, 7681, 7687, 7691, 7699, 7703, 7717, 7723, 7727, 7741, 7753, 7757, 7759, 7789, 7793, 7817, 7823, 7829, 7841, 7853, 7867, 7873, 7877, 7879, 7883, 7901, 7907, 7919, 7927, 7933, 7937, 7949, 7951, 7963, 7993, 8009, 8011, 8017, 8039, 8053, 8059, 8069, 8081, 8087, 8089, 8093, 8101, 8111, 8117, 8123, 8147, 8161, 8167, 8171, 8179, 8191, 8209, 8219, 8221, 8231, 8233, 8237, 8243, 8263, 8269, 8273, 8287, 8291, 8293, 8297, 8311, 8317, 8329, 8353, 8363, 8369, 8377, 8387, 8389, 8419, 8423, 8429, 8431, 8443, 8447, 8461, 8467, 8501, 8513, 8521, 8527, 8537, 8539, 8543, 8563, 8573, 8581, 8597, 8599, 8609, 8623, 8627, 8629, 8641, 8647, 8663, 8669, 8677, 8681, 8689, 8693, 8699, 8707, 8713, 8719, 8731, 8737, 8741, 8747, 8753, 8761, 8779, 8783, 8803, 8807, 8819, 8821, 8831, 8837, 8839, 8849, 8861, 8863, 8867, 8887, 8893, 8923, 8929, 8933, 8941, 8951, 8963, 8969, 8971, 8999, 9001, 9007, 9011, 9013, 9029, 9041, 9043, 9049, 9059, 9067, 9091, 9103, 9109, 9127, 9133, 9137, 9151, 9157, 9161, 9173, 9181, 9187, 9199, 9203, 9209, 9221, 9227, 9239, 9241, 9257, 9277, 9281, 9283, 9293, 9311, 9319, 9323, 9337, 9341, 9343, 9349, 9371, 9377, 9391, 9397, 9403, 9413, 9419, 9421, 9431, 9433, 9437, 9439, 9461, 9463, 9467, 9473, 9479, 9491, 9497, 9511, 9521, 9533, 9539, 9547, 9551, 9587, 9601, 9613, 9619, 9623, 9629, 9631, 9643, 9649, 9661, 9677, 9679, 9689, 9697, 9719, 9721, 9733, 9739, 9743, 9749, 9767, 9769, 9781, 9787, 9791, 9803, 9811, 9817, 9829, 9833, 9839, 9851, 9857, 9859, 9871, 9883, 9887, 9901, 9907, 9923, 9929, 9931, 9941, 9949, 9967, 9973]

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


end TFPS1

namespace TFPFastMask

/-- `pat d n` has a `1` at positions `0, d, 2d, ..., (n-1)d`; it is the geometric sum
`(2^(d*n) - 1) / (2^d - 1)` written as an explicit sum, which is what makes the
doubling construction below easy to verify. -/
def pat (d n : Nat) : Nat := ∑ i ∈ Finset.range n, 2 ^ (d * i)

/-- Doubling construction: `repAux span k acc` appends a copy of `acc` shifted by `span`
`k` times, so it turns `2^j` ones spaced `span` apart into `2^(j+k)` of them.
Its cost is `O(length)`, whereas the classical `(2^(d*count)-1)/(2^d-1)` costs
`O(length * d / 64)` because of the big division. -/
def repAux (span : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | k + 1, acc => repAux (2 * span) k (acc + (acc <<< span))

/-- Fast replacement for `RosserBitSieve.periodicMask`: ones every `d` bits, `count` of them.
`Nat.clog 2 count` doublings produce at least `count` ones, and the truncation by
`2 ^ (d * count)` keeps exactly the first `count`. -/
def fPeriodic (d count : Nat) : Nat :=
  repAux d (Nat.clog 2 count) 1 % 2 ^ (d * count)

def fDivisorMask (a len d : Nat) : Nat :=
  fPeriodic d ((len + d - 1) / d) * 2 ^ ((d - a % d) % d)

def fCompositeMask (ds : List Nat) (a len : Nat) : Nat :=
  ds.foldl (fun mask d => mask ||| fDivisorMask a len d) 0

def fCandidateMask (ds : List Nat) (a len : Nat) : Nat :=
  (2 ^ len - 1) ^^^ (fCompositeMask ds a len % 2 ^ len)

end TFPFastMask

end TFPS1



/-! Step 1: the doubling construction computes the same periodic mask as the
accepted `RosserBitSieve.periodicMask`. -/

namespace TFPS1

open Finset
open TFPS1

namespace TFPFastMask

open RosserBitSieve

theorem pat_zero (d : Nat) : pat d 0 = 0 := by simp [pat]

theorem pat_one (d : Nat) : pat d 1 = 1 := by simp [pat]

theorem pat_succ (d n : Nat) : pat d (n + 1) = pat d n + 2 ^ (d * n) := by
  simp [pat, Finset.sum_range_succ]

theorem pat_add (d m n : Nat) : pat d (m + n) = pat d m + 2 ^ (d * m) * pat d n := by
  induction n with
  | zero => simp [pat]
  | succ n ih =>
    have h : d * (m + n) = d * m + d * n := Nat.mul_add d m n
    rw [Nat.add_succ, pat_succ d (m + n), ih, pat_succ d n, h, pow_add]
    ring

theorem repAux_pat (d j k : Nat) :
    repAux (d * 2 ^ j) k (pat d (2 ^ j)) = pat d (2 ^ (j + k)) := by
  induction k generalizing j with
  | zero => simp [repAux]
  | succ k ih =>
    simp only [repAux, Nat.shiftLeft_eq_mul_pow]
    have h2 : 2 * (d * 2 ^ j) = d * 2 ^ (j + 1) := by ring
    rw [h2]
    have hacc : pat d (2 ^ j) + pat d (2 ^ j) * 2 ^ (d * 2 ^ j) = pat d (2 ^ (j + 1)) := by
      have h1 : (2 : Nat) ^ (j + 1) = 2 ^ j + 2 ^ j := by rw [pow_succ]; ring
      rw [h1, pat_add]
      ring
    rw [hacc, ih (j + 1)]
    rw [show j + 1 + k = j + (k + 1) by omega]

theorem repAux_pat_one (d k : Nat) : repAux d k 1 = pat d (2 ^ k) := by
  have h := repAux_pat d 0 k
  simp only [Nat.pow_zero, Nat.mul_one, Nat.zero_add] at h
  rwa [pat_one] at h

theorem pat_lt (d n : Nat) (hd : 0 < d) : pat d n < 2 ^ (d * n) := by
  induction n with
  | zero => simp [pat]
  | succ n ih =>
    rw [pat_succ d n, Nat.mul_succ, pow_add]
    have h2d : (2 : Nat) ≤ 2 ^ d := by
      calc (2 : Nat) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
    have h : (2 : Nat) ^ (d * n) * 2 ≤ 2 ^ (d * n) * 2 ^ d := Nat.mul_le_mul_left _ h2d
    have h2 : (2 : Nat) ^ (d * n) * 2 = 2 ^ (d * n) + 2 ^ (d * n) := by ring
    omega

theorem fPeriodic_eq_pat (d count : Nat) (hd : 0 < d) : fPeriodic d count = pat d count := by
  have hle : count ≤ 2 ^ Nat.clog 2 count := Nat.le_pow_clog (by norm_num) count
  have hbig : repAux d (Nat.clog 2 count) 1 = pat d (2 ^ Nat.clog 2 count) := repAux_pat_one d _
  unfold fPeriodic
  rw [hbig]
  have hsplit : (2 : Nat) ^ Nat.clog 2 count
      = count + (2 ^ Nat.clog 2 count - count) := (Nat.add_sub_cancel' hle).symm
  rw [hsplit, pat_add]
  have hmod : (pat d count + 2 ^ (d * count) * pat d (2 ^ Nat.clog 2 count - count))
      % 2 ^ (d * count) = pat d count := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (pat_lt d count hd)]
  exact hmod

theorem pat_eq_periodicMask (d count : Nat) (hd : 0 < d) :
    pat d count = periodicMask d count := by
  rw [periodicMask_eq_sum d count hd]
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_mul]

theorem fPeriodic_eq_periodicMask (d count : Nat) (hd : 0 < d) :
    fPeriodic d count = periodicMask d count := by
  rw [fPeriodic_eq_pat d count hd, pat_eq_periodicMask d count hd]

theorem fDivisorMask_eq (a len d : Nat) (hd : 0 < d) :
    fDivisorMask a len d = divisorMask a len d := by
  unfold fDivisorMask divisorMask
  rw [fPeriodic_eq_periodicMask d ((len + d - 1) / d) hd]

theorem fCompositeMask_eq (ds : List Nat) (a len : Nat) (hds : ∀ d ∈ ds, 0 < d) :
    fCompositeMask ds a len = compositeMask ds a len := by
  unfold fCompositeMask compositeMask
  suffices h : ∀ acc : Nat,
      ds.foldl (fun m d => m ||| fDivisorMask a len d) acc
        = ds.foldl (fun m d => m ||| divisorMask a len d) acc by
    simpa using h 0
  induction ds with
  | nil => intro acc; rfl
  | cons d ds ih =>
    intro acc
    simp only [List.foldl_cons]
    rw [fDivisorMask_eq a len d (hds d (by simp))]
    exact ih (fun e he => hds e (by simp [he])) _

theorem fCandidateMask_eq (ds : List Nat) (a len : Nat) (hds : ∀ d ∈ ds, 0 < d) :
    fCandidateMask ds a len = candidateMask ds a len := by
  unfold fCandidateMask candidateMask
  rw [fCompositeMask_eq ds a len hds]

end TFPFastMask

end TFPS1



/-! Step 1b: the divisor list contains *every* prime `<= 10^4`.

The certificate is a `decide +kernel` check that the explicit list equals
`(List.range 10001).filter isPrimeTrialSmall`, where `isPrimeTrialSmall` is trial division
by the 25 primes `<= 100` — enough below `101^2 = 10201`.  A naive `List.contains` scan
costs 368 s; the filter equality costs ~7 s. -/

namespace TFPS1

open TFPS1

namespace TFPFastMask

open RosserBitSieve RosserSieveData

/-- the primes `<= 100` -/
def l100 : List Nat :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]

theorem l100_eq : l100 = (List.range 101).filter (fun q => decide q.Prime) := by
  decide +kernel

theorem l100_prime {d : Nat} (hd : d ∈ l100) : d.Prime := by
  rw [l100_eq] at hd
  exact decide_eq_true_eq.mp (List.mem_filter.mp hd).2

theorem l100_complete {q : Nat} (hq : q.Prime) (hle : q ≤ 100) : q ∈ l100 := by
  rw [l100_eq]
  exact List.mem_filter.mpr ⟨List.mem_range.mpr (by omega), decide_eq_true_eq.mpr hq⟩

/-- primality test valid below `101^2`: no factor `d <= sqrt q` among the primes `<= 100` -/
def isPrimeTrialSmall (q : Nat) : Bool :=
  Nat.ble 2 q && l100.all (fun d => Nat.blt q (d * d) || q % d != 0)

theorem isPrimeTrialSmall_iff (q : Nat) (hq : q < 10001) :
    isPrimeTrialSmall q = true ↔ q.Prime := by
  rw [isPrimeTrialSmall, Bool.and_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨h2, hall⟩
    have h2' : 2 ≤ q := Nat.le_of_ble_eq_true h2
    by_contra hnp
    have hmp : q.minFac.Prime := Nat.minFac_prime (by omega)
    have hsq : q.minFac * q.minFac ≤ q := by
      have h := Nat.minFac_sq_le_self (by omega : 0 < q) hnp
      rwa [pow_two] at h
    have hm100 : q.minFac ≤ 100 := by
      by_contra hc
      have h101 : 101 ≤ q.minFac := by omega
      have h3 := le_trans (Nat.mul_le_mul h101 h101) hsq
      omega
    have hmem : q.minFac ∈ l100 := l100_complete hmp hm100
    have hmod : q % q.minFac = 0 := Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd q)
    have hb := hall q.minFac hmem
    have hblt : Nat.blt q (q.minFac * q.minFac) = false := by
      cases h : Nat.blt q (q.minFac * q.minFac) with
      | false => rfl
      | true => rw [Nat.blt_eq] at h; omega
    rw [hblt, Bool.false_or] at hb
    simp [hmod] at hb
  · intro hp
    refine ⟨Nat.ble_eq_true_of_le hp.two_le, ?_⟩
    intro d hd
    have hdp : d.Prime := l100_prime hd
    by_cases hblt : Nat.blt q (d * d) = true
    · simp [hblt]
    · have hbf : Nat.blt q (d * d) = false := by
        cases h : Nat.blt q (d * d) with
        | false => rfl
        | true => exact absurd h hblt
      rw [hbf, Bool.false_or]
      have hne : q % d ≠ 0 := by
        intro hmod
        have hdvd : d ∣ q := Nat.dvd_of_mod_eq_zero hmod
        have heq : d = q := (Nat.prime_dvd_prime_iff_eq hdp hp).mp hdvd
        have hle : d * d ≤ q := by
          by_contra hc
          exact hblt (by rw [Nat.blt_eq]; omega)
        subst heq
        nlinarith [hdp.two_le, hle]
      simp [hne]

/-- the explicit divisor list is exactly the primes below `10001` -/
theorem divisors_eq : divisors = (List.range 10001).filter isPrimeTrialSmall := by
  decide +kernel

/-- every prime `<= 10^4` occurs in the divisor list -/
theorem divisors_complete {q : Nat} (hq : q.Prime) (hle : q ≤ 10000) : q ∈ divisors := by
  rw [divisors_eq]
  exact List.mem_filter.mpr ⟨List.mem_range.mpr (by omega),
    (isPrimeTrialSmall_iff q (by omega)).mpr hq⟩

end TFPFastMask

end TFPS1



/-! Step 2a: the *converse* bit characterisation of the masks.

The accepted infrastructure only proves "prime ⟹ bit set" (coverage).  The θ lower bound
needs the other direction on the candidate mask, so here we characterise the bits exactly. -/

namespace TFPS1

open TFPS1

namespace TFPFastMask

open RosserBitSieve RosserSieveData

/-- bits of `pat d n` are exactly the multiples of `d` below `d * n` -/
theorem pat_testBit (d n j : Nat) (hd : 0 < d) :
    (pat d n).testBit j = true ↔ ∃ i, i < n ∧ j = d * i := by
  induction n with
  | zero => simp [pat]
  | succ n ih =>
    have hlt := pat_lt d n hd
    have h : pat d (n + 1) = 2 ^ (d * n) * 1 + pat d n := by
      rw [Nat.mul_one, pat_succ, Nat.add_comm]
    rw [h, Nat.testBit_two_pow_mul_add 1 hlt j]
    by_cases hj : j < d * n
    · rw [if_pos hj, ih]
      constructor
      · rintro ⟨i, hi, hji⟩; exact ⟨i, by omega, hji⟩
      · rintro ⟨i, hi, hji⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | h'
        · exact ⟨i, h', hji⟩
        · subst h'
          omega
    · rw [if_neg hj, Nat.testBit_one_eq_true_iff_self_eq_zero]
      constructor
      · intro h0
        exact ⟨n, by omega, by omega⟩
      · rintro ⟨i, hi, hji⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | h'
        · have hmul : d * i < d * n := Nat.mul_lt_mul_of_pos_left h' hd
          omega
        · subst h'
          omega

theorem periodicMask_testBit (d count j : Nat) (hd : 0 < d) :
    (periodicMask d count).testBit j = true ↔ ∃ i, i < count ∧ j = d * i := by
  rw [← pat_eq_periodicMask d count hd]
  exact pat_testBit d count j hd

end TFPFastMask

end TFPS1



/-! Step 2b: the converse direction for the divisor/composite/candidate masks —
"no divisor divides `a+i`" really does force `a+i` to be prime. -/

namespace TFPS1

open TFPS1

namespace TFPFastMask

open RosserBitSieve RosserSieveData

/-- the only `x < d` with `(a + x) % d = 0` is the offset used by `divisorMask` -/
theorem eq_off_of_mod {a d x : Nat} (hd : 0 < d) (hx : x < d) (h : (a + x) % d = 0) :
    x = (d - a % d) % d := by
  have hxmod : x % d = x := Nat.mod_eq_of_lt hx
  rw [Nat.add_mod, hxmod] at h
  have ha : a % d < d := Nat.mod_lt _ hd
  have hsum : a % d + x = 0 ∨ a % d + x = d := by
    have hlt : a % d + x < 2 * d := by omega
    obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero h
    have hc2 : c < 2 := by nlinarith
    have hc01 : c = 0 ∨ c = 1 := by omega
    rcases hc01 with h0 | h1
    · left; rw [h0, Nat.mul_zero] at hc; omega
    · right; rw [h1, Nat.mul_one] at hc; omega
  rcases hsum with h0 | h1
  · have hx0 : x = 0 := by omega
    have ha0 : a % d = 0 := by omega
    rw [hx0, ha0, Nat.sub_zero, Nat.mod_self]
  · have : d - a % d = x := by omega
    rw [this, Nat.mod_eq_of_lt hx]

/-- bit `i < len` of `divisorMask a len d` is set exactly when `d ∣ a + i` -/
theorem divisorMask_testBit (a len d i : Nat) (hd : 0 < d) (hi : i < len) :
    (divisorMask a len d).testBit i = true ↔ d ∣ a + i := by
  constructor
  · exact divisorMask_bit_dvd a len d i hd
  · intro hdiv
    set off := (d - a % d) % d with hoff
    have hoff_lt : off < d := by rw [hoff]; exact Nat.mod_lt _ hd
    have hoff_dvd : d ∣ a + off := by rw [hoff]; exact first_multiple a d hd
    have hoff_eq : off = i % d := by
      have hmodi : (a + i % d) % d = 0 := by
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.mod_eq_zero_of_dvd hdiv]
      rw [hoff]
      exact (eq_off_of_mod hd (Nat.mod_lt i hd) hmodi).symm
    have hoff_le : off ≤ i := by rw [hoff_eq]; exact Nat.mod_le i d
    have hdvd : d ∣ i - off := by
      obtain ⟨k1, hk1⟩ := hdiv
      obtain ⟨k2, hk2⟩ := hoff_dvd
      have hle : d * k2 ≤ d * k1 := by omega
      have hk21 : k2 ≤ k1 := Nat.le_of_mul_le_mul_left hle hd
      refine ⟨k1 - k2, ?_⟩
      have h1 : d * (k1 - k2) = d * k1 - d * k2 := Nat.mul_sub_left_distrib d k1 k2
      omega
    obtain ⟨k, hk⟩ := hdvd
    have hk_lt : k < (len + d - 1) / d := by
      have hle : d * k ≤ len - 1 := by
        have h1 : d * k ≤ i := by rw [← hk]; exact Nat.sub_le i off
        omega
      have h2 : (k + 1) * d ≤ len + d - 1 := by
        have h4 : d * (k + 1) ≤ len - 1 + d := by
          have h5 : d * (k + 1) = d * k + d := by ring
          omega
        have h6 : len - 1 + d = len + d - 1 := by omega
        rw [Nat.mul_comm (k + 1) d, ← h6]
        exact h4
      have h3 := (Nat.le_div_iff_mul_le hd).mpr h2
      omega
    have hbit : (periodicMask d ((len + d - 1) / d)).testBit (i - off) = true :=
      (periodicMask_testBit d _ (i - off) hd).mpr ⟨k, hk_lt, hk⟩
    rw [divisorMask, Nat.testBit_mul_two_pow,
      show decide (off ≤ i) = true from decide_eq_true_eq.mpr hoff_le, Bool.true_and, hbit]

end TFPFastMask

end TFPS1



/-! Step 2c: the soundness bridge — a set bit of the candidate mask really is a prime. -/

namespace TFPS1

open TFPS1

namespace TFPFastMask

open RosserBitSieve RosserSieveData

theorem divisors_pos {d : Nat} (hd : d ∈ divisors) : 0 < d := by
  have := divisors_ge_two d hd
  omega

/-- bit `i` of the composite mask is set iff some divisor divides `a + i` -/
theorem foldl_composite_testBit (ds : List Nat) :
    ∀ (acc a len i : Nat), i < len → (∀ d ∈ ds, 0 < d) →
      ((ds.foldl (fun m d => m ||| divisorMask a len d) acc).testBit i = true ↔
        acc.testBit i = true ∨ ∃ d ∈ ds, d ∣ a + i) := by
  induction ds with
  | nil => intro acc a len i _ _; simp
  | cons d ds ih =>
    intro acc a len i hi hds
    rw [List.foldl_cons,
      ih (acc ||| divisorMask a len d) a len i hi (fun q hq => hds q (by simp [hq])),
      Nat.testBit_or, Bool.or_eq_true, divisorMask_testBit a len d i (hds d (by simp)) hi]
    constructor
    · rintro ((ha | hd) | ⟨q, hq, hq'⟩)
      · exact Or.inl ha
      · exact Or.inr ⟨d, by simp, hd⟩
      · exact Or.inr ⟨q, by simp [hq], hq'⟩
    · rintro (ha | ⟨q, hq, hq'⟩)
      · exact Or.inl (Or.inl ha)
      · rcases List.mem_cons.mp hq with rfl | hq''
        · exact Or.inl (Or.inr hq')
        · exact Or.inr ⟨q, hq'', hq'⟩

theorem compositeMask_testBit (ds : List Nat) (a len i : Nat) (hds : ∀ d ∈ ds, 0 < d)
    (hi : i < len) :
    (compositeMask ds a len).testBit i = true ↔ ∃ d ∈ ds, d ∣ a + i := by
  unfold compositeMask
  have := foldl_composite_testBit ds 0 a len i hi hds
  simpa using this

/-- a set bit of the candidate mask is not divisible by any divisor -/
theorem candidateMask_no_dvd {ds : List Nat} {a len i : Nat} (hds : ∀ d ∈ ds, 0 < d)
    (hi : i < len) (h : (candidateMask ds a len).testBit i = true) :
    ¬ ∃ d ∈ ds, d ∣ a + i := by
  rw [candidateMask_bit] at h
  rw [decide_eq_true_eq.mpr hi, Bool.true_and] at h
  have hx : (compositeMask ds a len).testBit i = false := by
    cases hh : (compositeMask ds a len).testBit i with
    | false => rfl
    | true => rw [hh] at h; exact absurd h (by simp)
  intro hnex
  exact absurd ((compositeMask_testBit ds a len i hds hi).mpr hnex) (by rw [hx]; simp)

/-- **Soundness**: every set bit of the candidate mask over `[a+1, a+len]` is a prime. -/
theorem candidateMask_prime {a len i : Nat} (hi : i < len) (ha : 10000 < a)
    (hb : a + i ≤ 100000000) (h : (candidateMask divisors a len).testBit i = true) :
    (a + i).Prime := by
  have hno := candidateMask_no_dvd (fun d hd => divisors_pos hd) hi h
  by_contra hnp
  have hgt : 1 < a + i := by omega
  have hmp : (a + i).minFac.Prime := Nat.minFac_prime (by omega)
  have hdvd : (a + i).minFac ∣ a + i := Nat.minFac_dvd _
  have hsq : (a + i).minFac * (a + i).minFac ≤ a + i := by
    have h := Nat.minFac_sq_le_self (show 0 < a + i by omega) hnp
    rwa [pow_two] at h
  have hle : (a + i).minFac ≤ 10000 := by
    by_contra hc
    have h10001 : 10001 ≤ (a + i).minFac := by omega
    have h3 := le_trans (Nat.mul_le_mul h10001 h10001) hsq
    omega
  exact hno ⟨(a + i).minFac, divisors_complete hmp hle, hdvd⟩

end TFPFastMask

end TFPS1



/-! Step 3a: the two-term Taylor lower bound for `log`, which is what lets the θ chain
use only the aggregates `N, S = Σ(p−a), Q = Σ(p−a)²` that `packedMoments` returns. -/

namespace TFPS1

open TFPS1

namespace TFPFastMask

open RosserBitSieve RosserSieveData

/-- `log (1 + u) ≥ u − u²/2` for `u ≥ 0`.  Via the artanh series:
`z = u/(2+u) ≤ 1/3`, `log (1+u) = log ((1+z)/(1-z)) ≥ 2(z + z³/3) ≥ u − u²/2`. -/
theorem log_one_add_ge (u : Real) (hu : 0 ≤ u) : u - u ^ 2 / 2 ≤ Real.log (1 + u) := by
  have h2u : (0 : Real) < 2 + u := by linarith
  set z : Real := u / (2 + u) with hz
  have hz0 : 0 ≤ z := by rw [hz]; positivity
  have hz1 : z < 1 := by
    rw [hz, div_lt_one h2u]
    linarith
  have hratio : (1 + z) / (1 - z) = 1 + u := by
    rw [hz]; field_simp; ring
  have hser := Real.sum_range_le_log_div hz0 hz1 2
  rw [hratio] at hser
  have hsum : (∑ i ∈ Finset.range 2, z ^ (2 * (i : Nat) + 1) / (2 * (i : Nat) + 1))
      = z + z ^ 3 / 3 := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    norm_num
  rw [hsum] at hser
  have halg : u - u ^ 2 / 2 ≤ 2 * (z + z ^ 3 / 3) := by
    have key : 2 * (z + z ^ 3 / 3) - (u - u ^ 2 / 2)
        = u ^ 3 / (2 * (2 + u)) + 2 * u ^ 3 / (3 * (2 + u) ^ 3) := by
      rw [hz]; field_simp; ring
    have hnn : 0 ≤ u ^ 3 / (2 * (2 + u)) + 2 * u ^ 3 / (3 * (2 + u) ^ 3) := by positivity
    linarith
  set w : Real := z + z ^ 3 / 3 with hw
  have hw1 : w ≤ 1 / 2 * Real.log (1 + u) := by rw [hw]; exact hser
  have hw2 : u - u ^ 2 / 2 ≤ 2 * w := by rw [hw]; exact halg
  have hw3 : 2 * w ≤ Real.log (1 + u) := by linarith
  linarith

end TFPFastMask

end TFPS1



/-! Step 3b(1): a fixed-point rational lower bound for `log a`.

Write `a = 2^e * (1+t)` with `e = Nat.log2 a`, `t = (a - 2^e)/2^e` in `[0,1)`, and
`z = t/(2+t) = (a - 2^e)/(a + 2^e) <= 1/3`.  Then `a/2^e = (1+z)/(1-z)`, so by the artanh
series `log a >= e*log 2 + 2(z + z^3/3 + z^5/5)`.  Every term is positive, so truncation
is a lower bound; the truncation error is about 1.5e-4 nats while the chain needs 3e-3.

Scaling by `2^40` and flooring each term separately keeps everything in `Nat`. -/

namespace TFPS1

open TFPS1

namespace TFPFastMask

/-- floor of `0.6931471803 * 2^40`, a lower bound for `2^40 * log 2` -/
def K2 : Nat := 6931471803 * 2 ^ 40 / 10 ^ 10

theorem K2_le : (K2 : Real) ≤ 2 ^ 40 * Real.log 2 := by
  have h := Real.log_two_gt_d9
  have hK : (K2 : Real) ≤ (6931471803 : Real) * 2 ^ 40 / 10 ^ 10 := by
    rw [K2]
    have h1 : (((6931471803 * 2 ^ 40) / 10 ^ 10 : Nat) : Real)
        ≤ ((6931471803 * 2 ^ 40 : Nat) : Real) / ((10 ^ 10 : Nat) : Real) :=
      Nat.cast_div_le (α := Real)
    push_cast at h1
    linarith
  have h2 : (0 : Real) < 2 ^ 40 := by positivity
  nlinarith [h, hK]

/-- fixed-point lower bound: `logLo a ≤ 2^40 * log a` -/
def logLo (a : Nat) : Nat :=
  Nat.log2 a * K2
    + (2 ^ 41 * (a - 2 ^ Nat.log2 a)) / (a + 2 ^ Nat.log2 a)
    + (2 ^ 41 * (a - 2 ^ Nat.log2 a) ^ 3) / (3 * (a + 2 ^ Nat.log2 a) ^ 3)
    + (2 ^ 41 * (a - 2 ^ Nat.log2 a) ^ 5) / (5 * (a + 2 ^ Nat.log2 a) ^ 5)

theorem logLo_le_aux (e p num den a : Nat) (ha : 0 < a)
    (hp : p = 2 ^ e) (hpa : p ≤ a) (halt : a < 2 * p)
    (hnum : num = a - p) (hden : den = a + p) :
    ((e * K2 + (2 ^ 41 * num) / den + (2 ^ 41 * num ^ 3) / (3 * den ^ 3)
        + (2 ^ 41 * num ^ 5) / (5 * den ^ 5) : Nat) : Real) ≤ 2 ^ 40 * Real.log a := by
  have hp_pos : (0 : Nat) < p := by rw [hp]; positivity
  have hpR : (p : Real) = (2 : Real) ^ e := by rw [hp]; push_cast; ring
  have hnum_eq : (num : Real) = (a : Real) - p := by
    rw [hnum]; push_cast [Nat.cast_sub hpa]; ring
  have hden_eq : (den : Real) = (a : Real) + p := by rw [hden]; push_cast; ring
  have hden_pos : (0 : Real) < den := by rw [hden_eq]; positivity
  have hnum_lt : num < den := by rw [hnum, hden]; omega
  set z : Real := (num : Real) / den with hz
  have hz0 : 0 ≤ z := by rw [hz]; positivity
  have hz1 : z < 1 := by
    rw [hz, div_lt_one hden_pos]
    exact_mod_cast hnum_lt
  have hser := Real.sum_range_le_log_div hz0 hz1 3
  have hsum : (∑ i ∈ Finset.range 3, z ^ (2 * (i : Nat) + 1) / (2 * (i : Nat) + 1))
      = z + z ^ 3 / 3 + z ^ 5 / 5 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    norm_num
  rw [hsum] at hser
  have hratio : (1 + z) / (1 - z) = (a : Real) / p := by
    have hpne : (p : Real) ≠ 0 := by positivity
    have hdne : ((a : Real) + p) ≠ 0 := by positivity
    have hpm : (1 : Real) - z ≠ 0 := by
      intro h
      have hz1' : z = 1 := by linarith
      linarith [hz1]
    rw [div_eq_div_iff hpm hpne, hz, hnum_eq, hden_eq]
    field_simp
    ring
  rw [hratio] at hser
  have hlog : Real.log a = (e : Real) * Real.log 2 + Real.log ((a : Real) / p) := by
    have h := Real.log_div (x := (a : Real)) (y := (p : Real)) (by positivity) (by positivity)
    have h2 : Real.log ((p : Real)) = (e : Real) * Real.log 2 := by
      rw [hpR, Real.log_pow]
    rw [h2] at h
    linarith
  have h1 : (((2 ^ 41 * num) / den : Nat) : Real) ≤ 2 ^ 41 * z := by
    have h : (((2 ^ 41 * num) / den : Nat) : Real)
        ≤ ((2 ^ 41 * num : Nat) : Real) / ((den : Nat) : Real) := Nat.cast_div_le (α := Real)
    rw [hz]
    calc (((2 ^ 41 * num) / den : Nat) : Real)
        ≤ ((2 ^ 41 * num : Nat) : Real) / ((den : Nat) : Real) := h
      _ = 2 ^ 41 * ((num : Real) / den) := by push_cast; ring
  have h3 : (((2 ^ 41 * num ^ 3) / (3 * den ^ 3) : Nat) : Real) ≤ 2 ^ 41 * (z ^ 3 / 3) := by
    have h : (((2 ^ 41 * num ^ 3) / (3 * den ^ 3) : Nat) : Real)
        ≤ ((2 ^ 41 * num ^ 3 : Nat) : Real) / ((3 * den ^ 3 : Nat) : Real) :=
      Nat.cast_div_le (α := Real)
    rw [hz]
    calc (((2 ^ 41 * num ^ 3) / (3 * den ^ 3) : Nat) : Real)
        ≤ ((2 ^ 41 * num ^ 3 : Nat) : Real) / ((3 * den ^ 3 : Nat) : Real) := h
      _ = 2 ^ 41 * (((num : Real) / den) ^ 3 / 3) := by push_cast; ring
  have h5 : (((2 ^ 41 * num ^ 5) / (5 * den ^ 5) : Nat) : Real) ≤ 2 ^ 41 * (z ^ 5 / 5) := by
    have h : (((2 ^ 41 * num ^ 5) / (5 * den ^ 5) : Nat) : Real)
        ≤ ((2 ^ 41 * num ^ 5 : Nat) : Real) / ((5 * den ^ 5 : Nat) : Real) :=
      Nat.cast_div_le (α := Real)
    rw [hz]
    calc (((2 ^ 41 * num ^ 5) / (5 * den ^ 5) : Nat) : Real)
        ≤ ((2 ^ 41 * num ^ 5 : Nat) : Real) / ((5 * den ^ 5 : Nat) : Real) := h
      _ = 2 ^ 41 * (((num : Real) / den) ^ 5 / 5) := by push_cast; ring
  have hK : (e : Real) * K2 ≤ (e : Real) * (2 ^ 40 * Real.log 2) :=
    mul_le_mul_of_nonneg_left K2_le (Nat.cast_nonneg e)
  have hser' : 2 ^ 41 * (z + z ^ 3 / 3 + z ^ 5 / 5) ≤ 2 ^ 40 * Real.log ((a : Real) / p) := by
    nlinarith [hser]
  have hser'' : 2 ^ 41 * z + 2 ^ 41 * (z ^ 3 / 3) + 2 ^ 41 * (z ^ 5 / 5)
      ≤ 2 ^ 40 * Real.log ((a : Real) / p) := by
    have h : 2 ^ 41 * (z + z ^ 3 / 3 + z ^ 5 / 5)
        = 2 ^ 41 * z + 2 ^ 41 * (z ^ 3 / 3) + 2 ^ 41 * (z ^ 5 / 5) := by ring
    rw [h] at hser'
    exact hser'
  have hlog' : 2 ^ 40 * Real.log a
      = (e : Real) * (2 ^ 40 * Real.log 2) + 2 ^ 40 * Real.log ((a : Real) / p) := by
    rw [hlog]; ring
  have hsplit : ((e * K2 + (2 ^ 41 * num) / den + (2 ^ 41 * num ^ 3) / (3 * den ^ 3)
      + (2 ^ 41 * num ^ 5) / (5 * den ^ 5) : Nat) : Real)
      = (e * K2 : Real) + (((2 ^ 41 * num) / den : Nat) : Real)
        + (((2 ^ 41 * num ^ 3) / (3 * den ^ 3) : Nat) : Real)
        + (((2 ^ 41 * num ^ 5) / (5 * den ^ 5) : Nat) : Real) := by push_cast; ring
  have hsumF : (((2 ^ 41 * num) / den : Nat) : Real)
      + (((2 ^ 41 * num ^ 3) / (3 * den ^ 3) : Nat) : Real)
      + (((2 ^ 41 * num ^ 5) / (5 * den ^ 5) : Nat) : Real)
      ≤ 2 ^ 40 * Real.log ((a : Real) / p) := by
    linarith [h1, h3, h5, hser'']
  rw [hsplit, hlog']
  have hgoal : (e * K2 : Real) + (((2 ^ 41 * num) / den : Nat) : Real)
      + (((2 ^ 41 * num ^ 3) / (3 * den ^ 3) : Nat) : Real)
      + (((2 ^ 41 * num ^ 5) / (5 * den ^ 5) : Nat) : Real)
      = (e * K2 : Real) + ((((2 ^ 41 * num) / den : Nat) : Real)
        + (((2 ^ 41 * num ^ 3) / (3 * den ^ 3) : Nat) : Real)
        + (((2 ^ 41 * num ^ 5) / (5 * den ^ 5) : Nat) : Real)) := by ring
  rw [hgoal]
  exact add_le_add hK hsumF

theorem logLo_le (a : Nat) (ha : 0 < a) : (logLo a : Real) ≤ 2 ^ 40 * Real.log a := by
  have hlog2 : Nat.log2 a = Nat.log 2 a := Nat.log2_eq_log_two
  have hpa : 2 ^ Nat.log2 a ≤ a := by
    rw [hlog2]; exact Nat.pow_log_le_self 2 (by omega)
  have halt : a < 2 * 2 ^ Nat.log2 a := by
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) a
    rw [hlog2]
    calc a < 2 ^ (Nat.log 2 a).succ := h
      _ = 2 * 2 ^ Nat.log 2 a := by rw [Nat.succ_eq_add_one, pow_succ]; ring
  have := logLo_le_aux (Nat.log2 a) (2 ^ Nat.log2 a) (a - 2 ^ Nat.log2 a)
    (a + 2 ^ Nat.log2 a) a ha rfl hpa halt rfl rfl
  simpa only [logLo] using this

end TFPFastMask

end TFPS1



/-! Step 3b(2): the θ chain.

`stepA A c len` advances the accumulated fixed-point lower bound `A ≤ 2^40·θ c` across a
block `(c, c+len]` using the exact prime count/moments of the candidate mask; `chain`
walks a list of block lengths, checking at each checkpoint `c'` that `c' − 2√c' ≤ A/2^40`.

This file contains the checkpoint condition and the chain walk; `stepA_sound` (the
arithmetic content of one block) comes next. -/

namespace TFPS1

open TFPS1

namespace TFPFastMask

open RosserBitSieve RosserSieveData RosserBitMoments RosserPackedMoments
open RosserFastCompute

/-- the fixed-point scale -/
def TWO40 : Nat := 2 ^ 40

theorem TWO40_pos : (0 : Real) < (TWO40 : Real) := by rw [TWO40]; positivity

theorem TWO40_eq : ((TWO40 : Nat) : Real) = (2 : Real) ^ 40 := by rw [TWO40]; push_cast; ring

/-- checkpoint test: `c' − 2√c' ≤ A/2^40`, in exact integer arithmetic -/
def condA (A y : Nat) : Bool :=
  Nat.ble (y * TWO40) A || Nat.ble ((y * TWO40 - A) ^ 2) (4 * y * TWO40 * TWO40)

/-- `condA` really is the irrational comparison it encodes -/
theorem condA_bound {A y : Nat} (h : condA A y = true) :
    (y : Real) - 2 * Real.sqrt (y : Real) ≤ (A : Real) / 2 ^ 40 := by
  have hs0 : 0 ≤ Real.sqrt (y : Real) := Real.sqrt_nonneg _
  have hT : (0 : Real) < (2 : Real) ^ 40 := by positivity
  by_cases hc : y * TWO40 ≤ A
  · have hR : (y : Real) * 2 ^ 40 ≤ (A : Real) := by
      have h1 : ((y * TWO40 : Nat) : Real) ≤ (A : Real) := by exact_mod_cast hc
      rw [TWO40] at h1
      push_cast at h1
      linarith
    rw [le_div_iff₀ hT]
    nlinarith
  · have hc' : Nat.ble (y * TWO40) A = false := by
      cases hb : Nat.ble (y * TWO40) A with
      | false => rfl
      | true => exact absurd (Nat.le_of_ble_eq_true hb) hc
    simp only [condA] at h
    rw [hc', Bool.false_or] at h
    have h' := Nat.le_of_ble_eq_true h
    have hle : A ≤ y * TWO40 := by omega
    have hR : (((y * TWO40 - A) ^ 2 : Nat) : Real)
        ≤ ((4 * y * TWO40 * TWO40 : Nat) : Real) := by exact_mod_cast h'
    have hpos : (A : Real) ≤ (y : Real) * 2 ^ 40 := by
      have h1 : (A : Real) ≤ ((y * TWO40 : Nat) : Real) := by exact_mod_cast hle
      simp only [TWO40] at h1
      push_cast at h1
      linarith
    rw [Nat.cast_pow, Nat.cast_sub hle] at hR
    simp only [TWO40] at hR
    push_cast at hR
    have hB : (0 : Real) ≤ (y : Real) * 2 ^ 40 - (A : Real) := sub_nonneg.2 hpos
    have hC : (0 : Real) ≤ 2 * Real.sqrt (y : Real) * 2 ^ 40 := by positivity
    have hsq : ((y : Real) * 2 ^ 40 - (A : Real)) ^ 2
        ≤ (2 * Real.sqrt (y : Real) * 2 ^ 40) ^ 2 := by
      nlinarith [Real.sq_sqrt (show (0 : Real) ≤ (y : Real) by positivity)]
    have hle2 : (y : Real) * 2 ^ 40 - (A : Real) ≤ 2 * Real.sqrt (y : Real) * 2 ^ 40 := by
      nlinarith [hB, hC, hsq]
    rw [le_div_iff₀ hT]
    linarith

/-- `t ↦ t − 2√t` is strictly increasing on `[1, ∞)` -/
theorem sqrt_step {t y : Real} (ht : 1 ≤ t) (hty : t < y) :
    t - 2 * Real.sqrt t < y - 2 * Real.sqrt y := by
  have hs : Real.sqrt t < Real.sqrt y := Real.sqrt_lt_sqrt (by linarith) hty
  have h1 : 1 ≤ Real.sqrt t := by
    rw [show (1 : Real) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt ht
  have et := Real.sq_sqrt (by linarith : (0 : Real) ≤ t)
  have ey := Real.sq_sqrt (by linarith : (0 : Real) ≤ y)
  nlinarith [mul_pos (sub_pos.2 hs) (by linarith : (0 : Real) < Real.sqrt y + Real.sqrt t - 2)]

/-- a passing checkpoint gives the target inequality on the whole half-open block -/
theorem condA_sound {A c y : Nat} (hc1 : 1 ≤ c) (h : condA A y = true)
    (hA : (A : Real) / 2 ^ 40 ≤ Chebyshev.theta (c : Real)) :
    ∀ t : Real, (c : Real) ≤ t → t < (y : Real) → t - 2 * Real.sqrt t < Chebyshev.theta t := by
  intro t hct hty
  have h1t : (1 : Real) ≤ t := by
    have : (1 : Real) ≤ (c : Real) := by exact_mod_cast hc1
    linarith
  have hstep := sqrt_step h1t hty
  have hb := condA_bound h
  have hmono : Chebyshev.theta (c : Real) ≤ Chebyshev.theta t := Chebyshev.theta_mono hct
  linarith

/-- one block: advance the accumulated bound using the candidate mask's first moments.

`log (c+x) ≥ log c + x/c − x²/(2c²)`, and since every enumerated offset satisfies `x ≤ len`,
`Σ x²/(2c²) ≤ len·Σx/(2c²)`; so it suffices to add
`N·logLo c + 2^40·(Σx)·(2c − len)/(2c²)`.  (Dropping the second moment costs only
`O(1/(c log c))` nats per block, which is negligible against the chain's budget.) -/
def stepA (A c len : Nat) : Nat :=
  let pm := packedMoments (depthFor len) (fCandidateMask divisors (c + 1) len)
  A + pm.count * logLo c + (TWO40 * pm.first * (2 * c - len)) / (2 * c * c)

/-- walk a list of block lengths, checking `condA` at every checkpoint -/
def chain (st : Nat → Nat → Nat → Nat) (A c : Nat) : List Nat → Bool
  | [] => true
  | len :: l => condA A (c + len) && chain st (st A c len) (c + len) l

/-- if every step preserves a valid lower bound, the chain proves the target on
`[c, c + l.sum)` -/
theorem chain_sound (st : Nat → Nat → Nat → Nat)
    (hst : ∀ (A c len : Nat), (A : Real) / 2 ^ 40 ≤ Chebyshev.theta (c : Real) →
      (st A c len : Real) / 2 ^ 40 ≤ Chebyshev.theta ((c + len : Nat) : Real)) :
    ∀ (A c : Nat), 1 ≤ c →
      ∀ (l : List Nat), chain st A c l = true →
      (A : Real) / 2 ^ 40 ≤ Chebyshev.theta (c : Real) →
      ∀ t : Real, (c : Real) ≤ t → t < ((c + l.sum : Nat) : Real) →
        t - 2 * Real.sqrt t < Chebyshev.theta t := by
  intro A c hc1 l
  induction l generalizing A c with
  | nil =>
    intro h _ t hct hlt
    simp at hlt
    linarith
  | cons len l ih =>
    intro h hA t hct hlt
    simp only [chain, Bool.and_eq_true] at h
    obtain ⟨hcnd, htl⟩ := h
    by_cases ht : t < ((c + len : Nat) : Real)
    · exact condA_sound hc1 hcnd hA t hct ht
    · simp only [not_lt] at ht
      have hA' : (st A c len : Real) / 2 ^ 40
          ≤ Chebyshev.theta ((c + len : Nat) : Real) := hst A c len hA
      have hsum : ((c + (len :: l).sum : Nat) : Real) = (((c + len) + l.sum : Nat) : Real) := by
        push_cast [List.sum_cons]
        ring
      rw [hsum] at hlt
      exact ih (st A c len) (c + len) (by omega) htl hA' t ht hlt

end TFPFastMask

end TFPS1



/-! Step 3b(3): the per-block interface used by `stepA_sound` — the enumerated offsets of
the candidate mask are distinct primes in `(c, c+len]`, and their log-sum is at most
`θ(c+len) − θ(c)`. -/

namespace TFPS1

open TFPS1

namespace TFPFastMask

open RosserBitSieve RosserSieveData RosserBitMoments RosserPackedMoments
open RosserFastCompute

theorem fCandidateMask_lt (a len : Nat) : fCandidateMask divisors a len < 2 ^ len := by
  rw [fCandidateMask]
  apply Nat.xor_lt_two_pow
  · exact Nat.sub_lt (by positivity) (by norm_num)
  · exact Nat.mod_lt _ (by positivity)

/-- every enumerated offset is at most the block length -/
theorem enumBits_mem_le {c len x : Nat}
    (hx : x ∈ enumBits (depthFor len + 3) 1 (fCandidateMask divisors (c + 1) len)) :
    x ≤ len := by
  have hx' := hx
  rw [mem_enumBits] at hx'
  obtain ⟨hx1, _, hbit⟩ := hx'
  by_contra hcon
  have hlt : fCandidateMask divisors (c + 1) len < 2 ^ (x - 1) := by
    calc fCandidateMask divisors (c + 1) len < 2 ^ len := fCandidateMask_lt _ _
      _ ≤ 2 ^ (x - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [Nat.testBit_lt_two_pow hlt] at hbit
  exact Bool.noConfusion hbit

/-- every offset enumerated by the candidate mask gives a prime in `(c, c+len]` -/
theorem enumBits_prime {c len x : Nat} (hc : 10000 < c) (hbn : c + len ≤ 100000000)
    (hx : x ∈ enumBits (depthFor len + 3) 1 (fCandidateMask divisors (c + 1) len)) :
    (c + x).Prime ∧ c + x ≤ c + len := by
  rw [mem_enumBits] at hx
  obtain ⟨hx1, _, hbit⟩ := hx
  have hidx : x - 1 < len := by
    by_contra hcon
    have hlt : fCandidateMask divisors (c + 1) len < 2 ^ (x - 1) := by
      calc fCandidateMask divisors (c + 1) len < 2 ^ len := fCandidateMask_lt _ _
        _ ≤ 2 ^ (x - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow hlt] at hbit
    exact Bool.noConfusion hbit
  rw [fCandidateMask_eq divisors (c + 1) len (fun d hd => divisors_pos hd)] at hbit
  have hprime : (c + 1 + (x - 1)).Prime :=
    candidateMask_prime hidx (by omega) (by omega) hbit
  have heq : c + 1 + (x - 1) = c + x := by omega
  refine ⟨?_, by omega⟩
  rwa [heq] at hprime

/-- the log-sum over the enumerated offsets is at most `θ(c+len) − θ(c)` -/
theorem enumBits_theta {c len : Nat} (hc : 10000 < c) (hbn : c + len ≤ 100000000) :
    (List.map (fun x => Real.log (((c + x : Nat) : Real)))
        (enumBits (depthFor len + 3) 1 (fCandidateMask divisors (c + 1) len))).sum
      ≤ Chebyshev.theta (((c + len : Nat) : Real)) - Chebyshev.theta ((c : Nat) : Real) := by
  set L := enumBits (depthFor len + 3) 1 (fCandidateMask divisors (c + 1) len) with hL
  have hnd : L.Nodup := enumBits_nodup _ _ _
  have hinj : ∀ a ∈ L.toFinset, ∀ b ∈ L.toFinset, c + a = c + b → a = b := by
    intro a _ b _ hab; omega
  have h1 : (List.map (fun x => Real.log (((c + x : Nat) : Real))) L).sum
      = L.toFinset.sum (fun x => Real.log (((c + x : Nat) : Real))) :=
    (List.sum_toFinset (fun x => Real.log (((c + x : Nat) : Real))) hnd).symm
  have h2 : L.toFinset.sum (fun x => Real.log (((c + x : Nat) : Real)))
      = (L.toFinset.image (fun x => c + x)).sum (fun p => Real.log ((p : Nat) : Real)) := by
    rw [Finset.sum_image hinj]
  rw [h1, h2]
  -- the offsets give distinct primes in `(c, c+len]`
  have hsub : (L.toFinset.image (fun x => c + x))
      ⊆ Nat.primesLE (c + len) \ Nat.primesLE c := by
    intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨x, hx, rfl⟩ := hp
    rw [List.mem_toFinset] at hx
    obtain ⟨hprime, hle⟩ := enumBits_prime hc hbn hx
    have hxmem := (mem_enumBits (depthFor len + 3) 1 _ x).mp hx
    rw [Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesLE]
    exact ⟨⟨hle, hprime⟩, by omega⟩
  have hstep := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun p _ _ => Real.log_natCast_nonneg p)
  refine le_trans hstep ?_
  have hmono : Nat.primesLE c ⊆ Nat.primesLE (c + len) := Nat.primesLE_mono (by omega)
  have heq := Finset.sum_sdiff hmono (f := fun p : Nat => Real.log ((p : Nat) : Real))
  rw [← Chebyshev.theta_eq_sum_primesLE_log, ← Chebyshev.theta_eq_sum_primesLE_log] at heq
  linarith

end TFPFastMask

end TFPS1



/-! Step 3b(4): `stepA_sound` — one block preserves the accumulated lower bound for `θ`. -/

namespace TFPS1

open TFPS1

namespace TFPFastMask

open RosserBitSieve RosserSieveData RosserBitMoments RosserPackedMoments
open RosserFastCompute

/-- `depthFor` covers the length: `len ≤ 2^(depthFor len + 3)` -/
theorem len_le_pow_depthFor (len : Nat) : len ≤ 2 ^ (depthFor len + 3) := by
  unfold depthFor
  split_ifs with h
  · omega
  · have hk : (len - 1) / 8 < 2 ^ (Nat.log2 ((len - 1) / 8) + 1) := by
      have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ((len - 1) / 8)
      simpa [Nat.log2_eq_log_two, Nat.succ_eq_add_one] using h
    have h1 : len - 1 < 8 * ((len - 1) / 8 + 1) := by
      have hd := Nat.div_add_mod (len - 1) 8
      have hm := Nat.mod_lt (len - 1) (by norm_num : 0 < 8)
      omega
    have h2 : 8 * ((len - 1) / 8 + 1) ≤ 8 * 2 ^ (Nat.log2 ((len - 1) / 8) + 1) :=
      Nat.mul_le_mul_left 8 (by omega)
    have h3 : 8 * 2 ^ (Nat.log2 ((len - 1) / 8) + 1)
        = 2 ^ (Nat.log2 ((len - 1) / 8) + 1 + 3) := by
      rw [show (8 : Nat) = 2 ^ 3 by norm_num, ← pow_add]
      congr 1
      omega
    omega

/-- `∑ x ∈ L.toFinset, x` is the cast of `L.sum` -/
theorem list_toFinset_sum_cast (L : List Nat) (h : L.Nodup) :
    (L.toFinset).sum (fun x => (x : Real)) = (L.sum : Real) := by
  induction L with
  | nil => simp
  | cons a t ih =>
    rw [List.toFinset_cons, Finset.sum_insert, List.sum_cons,
      ih (List.nodup_cons.mp h).2]
    · push_cast; ring
    · simpa [List.mem_toFinset] using (List.nodup_cons.mp h).1

theorem stepA_sound {A c len : Nat} (hc : 10000 < c) (hbn : c + len ≤ 100000000)
    (hlen : 2 * len ≤ c) (hA : (A : Real) / 2 ^ 40 ≤ Chebyshev.theta (c : Real)) :
    (stepA A c len : Real) / 2 ^ 40 ≤ Chebyshev.theta ((c + len : Nat) : Real) := by
  have hcR : (0 : Real) < (c : Real) := by exact_mod_cast (by omega : 0 < c)
  set L := enumBits (depthFor len + 3) 1 (fCandidateMask divisors (c + 1) len) with hL
  have hnd : L.Nodup := enumBits_nodup _ _ _
  have hmsound : packedMoments (depthFor len) (fCandidateMask divisors (c + 1) len) = moments L := by
    rw [hL]
    refine packedMoments_sound _ _ ?_
    calc fCandidateMask divisors (c + 1) len < 2 ^ len := fCandidateMask_lt _ _
      _ ≤ 2 ^ (2 ^ (depthFor len + 3)) := Nat.pow_le_pow_right (by norm_num) (len_le_pow_depthFor len)
  -- the `Nat` division is a floor
  have hF : (stepA A c len : Real)
      ≤ (A : Real) + (L.length : Real) * (logLo c : Real)
        + (TWO40 : Real) * (L.sum : Real) * (2 * (c : Real) - (len : Real))
            / (2 * (c : Real) * (c : Real)) := by
    simp only [stepA, hmsound]
    have hcnt : (moments L).count = L.length := rfl
    have hfst : (moments L).first = L.sum := rfl
    rw [hcnt, hfst]
    have hcast : ((A + L.length * logLo c + (TWO40 * L.sum * (2 * c - len)) / (2 * c * c) : Nat) : Real)
        = (A : Real) + (L.length : Real) * (logLo c : Real)
          + (((TWO40 * L.sum * (2 * c - len)) / (2 * c * c) : Nat) : Real) := by
      push_cast; ring
    rw [hcast]
    have hdiv : (((TWO40 * L.sum * (2 * c - len)) / (2 * c * c) : Nat) : Real)
        ≤ ((TWO40 * L.sum * (2 * c - len) : Nat) : Real) / ((2 * c * c : Nat) : Real) :=
      Nat.cast_div_le (α := Real)
    have hsub : ((2 * c - len : Nat) : Real) = 2 * (c : Real) - (len : Real) := by
      rw [Nat.cast_sub (by omega : len ≤ 2 * c)]; push_cast; ring
    have hden : ((2 * c * c : Nat) : Real) = 2 * (c : Real) * (c : Real) := by push_cast; ring
    have hnum : ((TWO40 * L.sum * (2 * c - len) : Nat) : Real)
        = (TWO40 : Real) * (L.sum : Real) * (2 * (c : Real) - (len : Real)) := by
      push_cast [Nat.cast_sub (by omega : len ≤ 2 * c), TWO40]
      ring
    rw [hden, hnum] at hdiv
    linarith
  -- Taylor bound, summed over the enumerated offsets
  have hper : ∀ x ∈ L, Real.log (c : Real)
      + (x : Real) * ((2 * (c : Real) - (len : Real)) / (2 * (c : Real) ^ 2))
      ≤ Real.log (((c + x : Nat) : Real)) := by
    intro x hx
    have hxle : x ≤ len := enumBits_mem_le (by rwa [hL] at hx)
    have hx0 : (0 : Real) ≤ (x : Real) := Nat.cast_nonneg x
    have harg : ((c + x : Nat) : Real) = (c : Real) * (1 + (x : Real) / (c : Real)) := by
      push_cast; field_simp
    have hlog := log_one_add_ge ((x : Real) / (c : Real)) (by positivity)
    have hkey : (x : Real) * ((2 * (c : Real) - (len : Real)) / (2 * (c : Real) ^ 2))
        ≤ (x : Real) / (c : Real) - ((x : Real) / (c : Real)) ^ 2 / 2 := by
      have hxl : (x : Real) ≤ (len : Real) := by exact_mod_cast hxle
      rw [div_pow]
      field_simp
      nlinarith
    rw [harg, Real.log_mul (by positivity) (by positivity)]
    linarith
  have hsum_le : (L.length : Real) * Real.log (c : Real)
      + (L.sum : Real) * ((2 * (c : Real) - (len : Real)) / (2 * (c : Real) ^ 2))
      ≤ (List.map (fun x => Real.log (((c + x : Nat) : Real))) L).sum := by
    rw [← List.sum_toFinset (fun x => Real.log (((c + x : Nat) : Real))) hnd]
    have hsplit : (L.toFinset).sum (fun x => Real.log (c : Real)
          + (x : Real) * ((2 * (c : Real) - (len : Real)) / (2 * (c : Real) ^ 2)))
        = (L.length : Real) * Real.log (c : Real)
          + (L.sum : Real) * ((2 * (c : Real) - (len : Real)) / (2 * (c : Real) ^ 2)) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul]
      have hcard : (L.toFinset.card : Real) = (L.length : Real) := by
        rw [List.toFinset_card_of_nodup hnd]
      have hsum' : (L.toFinset).sum (fun x => (x : Real)) = (L.sum : Real) :=
        list_toFinset_sum_cast L hnd
      rw [hcard, hsum']
    rw [← hsplit]
    exact Finset.sum_le_sum (fun x hx => hper x (by rwa [List.mem_toFinset] at hx))
  have htheta := enumBits_theta (c := c) (len := len) hc hbn
  simp only [← hL] at htheta
  -- assemble
  have hG : (0 : Real) < 2 ^ 40 := by positivity
  have hA' : (A : Real) ≤ 2 ^ 40 * Chebyshev.theta (c : Real) := by
    have h2 : (0 : Real) < 2 ^ 40 := by positivity
    rw [div_le_iff₀ h2] at hA
    linarith
  -- rewrite the quadratic correction of `hF` into the grouped shape
  have hF' : (stepA A c len : Real)
      ≤ (A : Real) + (L.length : Real) * (logLo c : Real)
        + 2 ^ 40 * ((L.sum : Real)
            * ((2 * (c : Real) - (len : Real)) / (2 * (c : Real) ^ 2))) := by
    have hEq : 2 ^ 40 * (L.sum : Real) * (2 * (c : Real) - (len : Real))
          / (2 * (c : Real) * (c : Real))
        = 2 ^ 40 * ((L.sum : Real)
            * ((2 * (c : Real) - (len : Real)) / (2 * (c : Real) ^ 2))) := by
      have hden : (2 : Real) * (c : Real) * (c : Real) = 2 * (c : Real) ^ 2 := by ring
      rw [div_eq_mul_inv, div_eq_mul_inv, hden]
      ring
    rw [TWO40_eq] at hF
    rw [hEq] at hF
    exact hF
  have hlogLo' : (L.length : Real) * (logLo c : Real)
      ≤ 2 ^ 40 * ((L.length : Real) * Real.log (c : Real)) := by
    have h := mul_le_mul_of_nonneg_left (logLo_le c (by omega))
      (Nat.cast_nonneg (α := Real) L.length)
    calc (L.length : Real) * (logLo c : Real)
        ≤ (L.length : Real) * (2 ^ 40 * Real.log (c : Real)) := h
      _ = 2 ^ 40 * ((L.length : Real) * Real.log (c : Real)) := by ring
  have h1 : (stepA A c len : Real) ≤ 2 ^ 40 * Chebyshev.theta (c : Real)
      + 2 ^ 40 * ((L.length : Real) * Real.log (c : Real))
      + 2 ^ 40 * ((L.sum : Real)
          * ((2 * (c : Real) - (len : Real)) / (2 * (c : Real) ^ 2))) := by
    linarith [hF', hlogLo', hA']
  have hmul := mul_le_mul_of_nonneg_left hsum_le (le_of_lt hG)
  have hthetam := mul_le_mul_of_nonneg_left htheta (le_of_lt hG)
  have hexp : 2 ^ 40 * ((L.length : Real) * Real.log (c : Real)
        + (L.sum : Real) * ((2 * (c : Real) - (len : Real)) / (2 * (c : Real) ^ 2)))
      = 2 ^ 40 * ((L.length : Real) * Real.log (c : Real))
        + 2 ^ 40 * ((L.sum : Real)
            * ((2 * (c : Real) - (len : Real)) / (2 * (c : Real) ^ 2))) := by ring
  rw [hexp] at hmul
  have hmid : 2 ^ 40 * ((L.length : Real) * Real.log (c : Real))
      + 2 ^ 40 * ((L.sum : Real)
          * ((2 * (c : Real) - (len : Real)) / (2 * (c : Real) ^ 2)))
      ≤ 2 ^ 40 * (Chebyshev.theta ((c + len : Nat) : Real) - Chebyshev.theta (c : Real)) :=
    le_trans hmul hthetam
  have h2 : 2 ^ 40 * Chebyshev.theta (c : Real)
      + 2 ^ 40 * ((L.length : Real) * Real.log (c : Real))
      + 2 ^ 40 * ((L.sum : Real)
          * ((2 * (c : Real) - (len : Real)) / (2 * (c : Real) ^ 2)))
      ≤ 2 ^ 40 * Chebyshev.theta ((c + len : Nat) : Real) := by
    have hth : 2 ^ 40 * Chebyshev.theta (c : Real)
        + 2 ^ 40 * (Chebyshev.theta ((c + len : Nat) : Real) - Chebyshev.theta (c : Real))
        = 2 ^ 40 * Chebyshev.theta ((c + len : Nat) : Real) := by ring
    linarith [hmid, hth]
  rw [div_le_iff₀ hG]
  linarith [h1, h2]

end TFPFastMask

end TFPS1



/-! Step 3c: window slicing.

One mask covers a long block; the individual chain steps cut their window out of it with a
shift, so the 1229-divisor sieve is evaluated once per block instead of once per step. -/

namespace TFPS1

open TFPS1

namespace TFPFastMask

open RosserBitSieve RosserSieveData RosserBitMoments RosserPackedMoments
open RosserFastCompute

theorem divisors_prime {d : Nat} (hd : d ∈ divisors) : d.Prime := by
  rw [divisors_eq] at hd
  obtain ⟨hmem, hb⟩ := List.mem_filter.mp hd
  exact (isPrimeTrialSmall_iff d (by simpa using List.mem_range.mp hmem)).mp hb

theorem divisors_le {d : Nat} (hd : d ∈ divisors) : d ≤ 10000 := by
  rw [divisors_eq] at hd
  have hmem := (List.mem_filter.mp hd).1
  have := List.mem_range.mp hmem
  omega

theorem not_dvd_of_prime {A i : Nat} (hA : 10000 < A) (hp : (A + i).Prime) :
    ¬ ∃ d ∈ divisors, d ∣ A + i := by
  rintro ⟨d, hd, hdvd⟩
  have hdp : d.Prime := divisors_prime hd
  have hdle : d ≤ 10000 := divisors_le hd
  have hdeq : d = A + i := (Nat.prime_dvd_prime_iff_eq hdp hp).mp hdvd
  omega

/-- **exactness**: bit `i` of the fast candidate mask is set iff `A + i` is prime -/
theorem fCandidateMask_testBit {A len i : Nat} (hi : i < len) (hA : 10000 < A)
    (hb : A + i ≤ 100000000) :
    (fCandidateMask divisors A len).testBit i = true ↔ (A + i).Prime := by
  rw [fCandidateMask_eq divisors A len (fun d hd => divisors_pos hd)]
  constructor
  · intro h
    exact candidateMask_prime hi hA hb h
  · intro hp
    rw [candidateMask_bit, decide_eq_true hi, Bool.true_and]
    have hno := not_dvd_of_prime hA hp
    have hc : (compositeMask divisors A len).testBit i = false := by
      cases hh : (compositeMask divisors A len).testBit i with
      | false => rfl
      | true =>
        exact absurd ((compositeMask_testBit divisors A len i
          (fun d hd => divisors_pos hd) hi).mp hh) hno
    rw [hc]
    simp

/-- cutting a bit window out of a mask -/
theorem testBit_slice {M s δ i : Nat} (hi : i < δ) :
    (M / 2 ^ s % 2 ^ δ).testBit i = M.testBit (s + i) := by
  rw [Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and,
    Nat.testBit_div_two_pow, Nat.add_comm]

/-- **slicing**: a window of the sieve mask is the sieve mask of the shifted base -/
theorem fCandidateMask_slice {A L s δ : Nat} (hA : 10000 < A) (hL : A + L ≤ 100000000)
    (hs : s + δ ≤ L) :
    (fCandidateMask divisors (A + 1) L) / 2 ^ s % 2 ^ δ = fCandidateMask divisors (A + s + 1) δ := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < δ
  · rw [testBit_slice hi, Bool.eq_iff_iff,
      fCandidateMask_testBit (A := A + 1) (len := L) (i := s + i) (by omega) (by omega) (by omega),
      fCandidateMask_testBit (A := A + s + 1) (len := δ) (i := i) hi (by omega) (by omega)]
    have heq : A + 1 + (s + i) = A + s + 1 + i := by omega
    rw [heq]
  · have hδi : δ ≤ i := Nat.le_of_not_lt hi
    have hb1 : (fCandidateMask divisors (A + 1) L / 2 ^ s % 2 ^ δ).testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (Nat.mod_lt _ (by positivity))
        (Nat.pow_le_pow_right (by norm_num) hδi))
    have hb2 : (fCandidateMask divisors (A + s + 1) δ).testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (fCandidateMask_lt _ _)
        (Nat.pow_le_pow_right (by norm_num) hδi))
    rw [hb1, hb2]

/-- one window step: the bound at `x + δ` from the bound at `x`, using the window
`(x, x+δ]` = shift `s` of the block mask `M` -/
def stepW (M s B x δ : Nat) : Nat :=
  let win := M / 2 ^ s % 2 ^ δ
  let pm := packedMoments (depthFor δ) win
  B + pm.count * logLo x + (TWO40 * pm.first * (2 * x - δ)) / (2 * x * x)

theorem stepW_eq_stepA {M A L s x δ B : Nat} (hM : M = fCandidateMask divisors (A + 1) L)
    (hA : 10000 < A) (hL : A + L ≤ 100000000) (hx : x = A + s) (hs : s + δ ≤ L) :
    stepW M s B x δ = stepA B x δ := by
  subst hx
  have hsl := fCandidateMask_slice (A := A) (L := L) (s := s) (δ := δ) hA hL hs
  simp only [stepW, stepA, hM, hsl]

/-- soundness of one window step -/
theorem stepW_sound {M A L s x δ B : Nat} (hM : M = fCandidateMask divisors (A + 1) L)
    (hA : 10000 < A) (hL : A + L ≤ 100000000) (hx : x = A + s) (hs : s + δ ≤ L)
    (hc : 10000 < x) (hbn : x + δ ≤ 100000000) (hlen : 2 * δ ≤ x)
    (hB : (B : Real) / 2 ^ 40 ≤ Chebyshev.theta (x : Real)) :
    (stepW M s B x δ : Real) / 2 ^ 40 ≤ Chebyshev.theta ((x + δ : Nat) : Real) := by
  rw [stepW_eq_stepA hM hA hL hx hs]
  exact stepA_sound hc hbn hlen hB

/-- walk `n` windows of length `δ`; returns the final lower bound and whether all
checkpoint tests passed -/
def chainW (M : Nat) : Nat → Nat → Nat → Nat → Nat → Nat × Bool
  | 0, _, B, _, _ => (B, true)
  | n + 1, s, B, x, δ =>
    let r := chainW M n (s + δ) (stepW M s B x δ) (x + δ) δ
    (r.1, condA B (x + δ) && r.2)

/-- **soundness of the window chain**: a passing chain proves the target on
`[x, x + n·δ)` and carries the lower bound to `x + n·δ` -/
theorem chainW_sound {M A L δ : Nat} (hM : M = fCandidateMask divisors (A + 1) L)
    (hA : 10000 < A) (hL : A + L ≤ 100000000) (hδ : 0 < δ) :
    ∀ (n s x B R : Nat), x = A + s → s + n * δ ≤ L → 10000 < x → 2 * δ ≤ x →
      (B : Real) / 2 ^ 40 ≤ Chebyshev.theta (x : Real) → chainW M n s B x δ = (R, true) →
        (∀ m : Nat, x ≤ m → m + 1 ≤ x + n * δ →
            ((m : Real) + 1) - 2 * Real.sqrt ((m : Real) + 1) ≤ Chebyshev.theta (m : Real)) ∧
        (R : Real) / 2 ^ 40 ≤ Chebyshev.theta (((x + n * δ : Nat)) : Real) := by
  intro n
  induction n with
  | zero =>
    intro s x B R hx _ _ _ hB hEq
    have hconj : B = R ∧ True := by simpa only [chainW, Prod.mk.injEq] using hEq
    have hRB : B = R := hconj.1
    constructor
    · intro m hx1 hx2
      omega
    · rw [← hRB]
      simpa only [Nat.zero_mul, Nat.add_zero] using hB
  | succ n ih =>
    intro s x B R hx hs hc hlen hB hEq
    have hEq' : (chainW M n (s + δ) (stepW M s B x δ) (x + δ) δ).1 = R ∧
        (condA B (x + δ) && (chainW M n (s + δ) (stepW M s B x δ) (x + δ) δ).2) = true := by
      simpa only [chainW, Prod.mk.injEq] using hEq
    obtain ⟨hR, hchk⟩ := hEq'
    have hchk' : condA B (x + δ) = true ∧
        (chainW M n (s + δ) (stepW M s B x δ) (x + δ) δ).2 = true := by
      simpa only [Bool.and_eq_true] using hchk
    obtain ⟨hchk1, hchk2⟩ := hchk'
    have hrec : chainW M n (s + δ) (stepW M s B x δ) (x + δ) δ = (R, true) :=
      Prod.ext hR hchk2
    have hmul : (n + 1) * δ = n * δ + δ := by ring
    have hy : x + δ = A + (s + δ) := by omega
    have hs' : s + δ + n * δ ≤ L := by rw [hmul] at hs; omega
    have hc' : 10000 < x + δ := by omega
    have hlen' : 2 * δ ≤ x + δ := by omega
    have hbn : x + δ ≤ 100000000 := by omega
    have hsδ : s + δ ≤ L := by rw [hmul] at hs; omega
    have hB' : (stepW M s B x δ : Real) / 2 ^ 40 ≤ Chebyshev.theta ((x + δ : Nat) : Real) :=
      stepW_sound hM hA hL hx hsδ hc hbn hlen hB
    obtain ⟨hcov, hacc⟩ := ih (s + δ) (x + δ) (stepW M s B x δ) R hy hs' hc' hlen' hB' hrec
    have hxy : x + (n + 1) * δ = x + δ + n * δ := by ring
    constructor
    · intro m hm1 hm2
      by_cases hlt : m + 1 ≤ x + δ
      · have hbase := condA_bound hchk1
        have hmono : Chebyshev.theta (x : Real) ≤ Chebyshev.theta (m : Real) := by
          apply Chebyshev.theta_mono
          exact_mod_cast hm1
        have h1 : (1 : Real) ≤ (((m + 1 : Nat)) : Real) := by
          have : (0 : Real) ≤ ((m : Nat) : Real) := Nat.cast_nonneg m
          push_cast
          linarith
        have hle : (((m + 1 : Nat)) : Real) ≤ (((x + δ : Nat)) : Real) := by exact_mod_cast hlt
        have hstep : (((m + 1 : Nat)) : Real) - 2 * Real.sqrt (((m + 1 : Nat)) : Real)
            ≤ ((x + δ : Nat) : Real) - 2 * Real.sqrt (((x + δ : Nat)) : Real) := by
          rcases lt_or_eq_of_le hle with hlt' | heq
          · exact le_of_lt (sqrt_step h1 hlt')
          · rw [heq]
        have hm1' : (((m : Nat)) : Real) + 1 = (((m + 1 : Nat)) : Real) := by push_cast; ring
        rw [hm1']
        linarith
      · have hge : x + δ ≤ m := by omega
        exact hcov m hge (by rw [hxy] at hm2; exact hm2)
    · rw [hxy]
      exact hacc

end TFPFastMask

end TFPS1



/-! Step 4: the bootstrap `θ(10^4)` lower bound and the shard interface. -/

namespace TFPS1

open TFPS1

namespace TFPFastMask

open RosserBitSieve RosserSieveData RosserBitMoments RosserPackedMoments
open RosserFastCompute

theorem sum_map_cast (L : List Nat) (f : Nat → Nat) :
    ((L.map f).sum : Real) = (L.map (fun x : Nat => (f x : Real))).sum := by
  induction L with
  | nil => simp
  | cons a t ih => simp [ih]

theorem sum_map_mul_left (L : List Nat) (c : Real) (f : Nat → Real) :
    (L.map (fun x : Nat => c * f x)).sum = c * (L.map f).sum := by
  induction L with
  | nil => simp
  | cons a t ih => simp [ih]; ring

theorem list_sum_le_sum {L : List Nat} {f g : Nat → Real} (h : ∀ x ∈ L, f x ≤ g x) :
    (L.map f).sum ≤ (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h a (by simp)) (ih (fun x hx => h x (by simp [hx])))

theorem divisors_nodup : divisors.Nodup := by
  rw [divisors_eq]
  exact (List.nodup_range (n := 10001)).filter isPrimeTrialSmall

/-- generic form: the log-sum over a list of distinct primes `≤ 10^4` is at most `θ(10^4)` -/
theorem list_log_sum_le_theta {L : List Nat} (hnd : L.Nodup)
    (hp : ∀ d ∈ L, d.Prime) (hle : ∀ d ∈ L, d ≤ 10000) :
    (L.map (fun d : Nat => Real.log (d : Real))).sum ≤ Chebyshev.theta (10000 : Real) := by
  have h1 : (L.map (fun d : Nat => Real.log (d : Real))).sum
      = (L.toFinset).sum (fun d : Nat => Real.log (d : Real)) :=
    (List.sum_toFinset (fun d : Nat => Real.log (d : Real)) hnd).symm
  have h2 : Chebyshev.theta (10000 : Real)
      = (Nat.primesLE 10000).sum (fun p : Nat => Real.log (p : Real)) := by
    simpa using Chebyshev.theta_eq_sum_primesLE_log 10000
  rw [h1, h2]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    rw [List.mem_toFinset] at hd
    exact Nat.mem_primesLE.mpr ⟨hle d hd, hp d hd⟩
  · intro x hx _
    exact Real.log_nonneg (by
      have h2 : x.Prime := Nat.prime_of_mem_primesLE hx
      have : (1 : Real) ≤ (x : Real) := by exact_mod_cast h2.one_le
      linarith)

/-- generic bootstrap: the fixed-point sum of `logLo` over a list of primes is a lower
bound for `θ` at the next integer -/
theorem list_sum_logLo_le_theta {L : List Nat} (hnd : L.Nodup) (hpos : ∀ d ∈ L, 0 < d)
    (hp : ∀ d ∈ L, d.Prime) (hle : ∀ d ∈ L, d ≤ 10000) :
    (((L.map logLo).sum : Nat) : Real) / 2 ^ 40 ≤ Chebyshev.theta (10001 : Real) := by
  have hcast := sum_map_cast L logLo
  have hle1 : (L.map (fun d : Nat => (logLo d : Real))).sum
      ≤ (L.map (fun d : Nat => 2 ^ 40 * Real.log (d : Real))).sum :=
    list_sum_le_sum (f := fun d : Nat => (logLo d : Real))
      (g := fun d : Nat => 2 ^ 40 * Real.log (d : Real))
      (fun d hd => logLo_le d (hpos d hd))
  have hle2 : (L.map (fun d : Nat => 2 ^ 40 * Real.log (d : Real))).sum
      = 2 ^ 40 * (L.map (fun d : Nat => Real.log (d : Real))).sum :=
    sum_map_mul_left L (2 ^ 40) (fun d : Nat => Real.log (d : Real))
  have hlog := list_log_sum_le_theta hnd hp hle
  have hmono : Chebyshev.theta (10000 : Real) ≤ Chebyshev.theta (10001 : Real) :=
    Chebyshev.theta_mono (by norm_num)
  have hmain : ((L.map logLo).sum : Real) ≤ 2 ^ 40 * Chebyshev.theta (10001 : Real) := by
    rw [hle2] at hle1
    linarith
  rw [div_le_iff₀ (by positivity : (0 : Real) < 2 ^ 40)]
  linarith

/-- the explicit fixed-point lower bound for `θ(10^4)` -/
theorem divisors_theta_bound :
    (((divisors.map logLo).sum : Nat) : Real) / 2 ^ 40 ≤ Chebyshev.theta (10001 : Real) :=
  list_sum_logLo_le_theta divisors_nodup (fun d hd => divisors_pos hd)
    (fun d hd => divisors_prime hd) (fun d hd => divisors_le hd)

/-- the shard interface: a passing window chain gives the target on `[A, A+N·δ)` and the
quantitative carry at `A + N·δ` -/
theorem chainW_shard {M A L δ N B R : Nat} (hM : M = fCandidateMask divisors (A + 1) L)
    (hA : 10000 < A) (hL : A + L ≤ 100000000) (hδ : 0 < δ) (hNL : N * δ ≤ L)
    (hlen : 2 * δ ≤ A) (hB : (B : Real) / 2 ^ 40 ≤ Chebyshev.theta (A : Real))
    (hcert : chainW M N 0 B A δ = (R, true)) :
    (∀ n : Nat, A ≤ n → n + 1 ≤ A + N * δ →
        ((n : Real) + 1) - 2 * Real.sqrt ((n : Real) + 1) ≤ Chebyshev.theta (n : Real)) ∧
      (R : Real) / 2 ^ 40 ≤ Chebyshev.theta ((A + N * δ : Nat) : Real) :=
  chainW_sound hM hA hL hδ N 0 A B R rfl (by simpa using hNL) hA hlen hB hcert

end TFPFastMask

end TFPS1



/-! Step 5: the adaptive window chain.

The checkpoint slack `B/2^40 - (x - 2√x)` fluctuates (it is the margin `2√x - err x` minus the
accumulated deficit), so a fixed window length cannot survive a long run.  `nextD` takes a fixed
fraction of the current slack, and every step re-checks `condA`. -/

namespace TFPS1

open TFPS1

namespace TFPFastMask

open RosserBitSieve RosserSieveData RosserBitMoments RosserPackedMoments
open RosserFastCompute

/-- the checkpoint slack, in units of `2^-40`: `B/2^40 + 2√x - x` (with `√` floored, so this
is a lower bound for the true slack) -/
def slack (B x : Nat) : Nat :=
  (B + 2 * TWO40 * Nat.sqrt x - x * TWO40) / TWO40

/-- adaptive window length: the slack minus a safety gap of a third (at least 40) -/
def nextD (B x : Nat) : Nat :=
  max 5 (slack B x - max 40 (slack B x / 3))

/-- the adaptive chain: walk while `nextD` steps still pass the checkpoint test; returns the
final position, the final lower bound, and whether every test passed -/
def chainD (M L : Nat) : Nat → Nat → Nat → Nat → Nat × Nat × Bool
  | 0, _, B, x => (x, B, true)
  | n + 1, s, B, x =>
    let δ := nextD B x
    let r := chainD M L n (s + δ) (stepW M s B x δ) (x + δ)
    (r.1, r.2.1, condA B (x + δ) && decide (s + δ ≤ L) && decide (2 * δ ≤ x) && r.2.2)

/-- **soundness of the adaptive chain** -/
theorem chainD_sound {M A L : Nat} (hM : M = fCandidateMask divisors (A + 1) L)
    (hA : 10000 < A) (hL : A + L ≤ 100000000) :
    ∀ (n s x B X R : Nat), x = A + s → (B : Real) / 2 ^ 40 ≤ Chebyshev.theta (x : Real) →
      chainD M L n s B x = (X, R, true) →
        (∀ m : Nat, x ≤ m → m + 1 ≤ X →
            ((m : Real) + 1) - 2 * Real.sqrt ((m : Real) + 1) ≤ Chebyshev.theta (m : Real)) ∧
        (R : Real) / 2 ^ 40 ≤ Chebyshev.theta (X : Real) := by
  intro n
  induction n with
  | zero =>
    intro s x B X R hx hB hEq
    have hconj : x = X ∧ B = R ∧ True := by simpa only [chainD, Prod.mk.injEq] using hEq
    have h1 : x = X := hconj.1
    have h2 : B = R := hconj.2.1
    subst h1
    subst h2
    constructor
    · intro m hm1 hm2
      omega
    · simpa using hB
  | succ n ih =>
    intro s x B X R hx hB hEq
    have hEq' : (chainD M L n (s + nextD B x) (stepW M s B x (nextD B x)) (x + nextD B x)).1 = X ∧
        (chainD M L n (s + nextD B x) (stepW M s B x (nextD B x)) (x + nextD B x)).2.1 = R ∧
        (condA B (x + nextD B x) && decide (s + nextD B x ≤ L) &&
          decide (2 * nextD B x ≤ x) &&
          (chainD M L n (s + nextD B x) (stepW M s B x (nextD B x)) (x + nextD B x)).2.2) = true := by
      simpa only [chainD, Prod.mk.injEq] using hEq
    obtain ⟨hX, hR, hchk⟩ := hEq'
    have hchk1 : condA B (x + nextD B x) = true := (by
      simp only [Bool.and_eq_true] at hchk; exact hchk.1.1.1)
    have hlen1 : decide (s + nextD B x ≤ L) = true := (by
      simp only [Bool.and_eq_true] at hchk; exact hchk.1.1.2)
    have hlen2 : decide (2 * nextD B x ≤ x) = true := (by
      simp only [Bool.and_eq_true] at hchk; exact hchk.1.2)
    have hrec : (chainD M L n (s + nextD B x) (stepW M s B x (nextD B x))
        (x + nextD B x)).2.2 = true := (by
      simp only [Bool.and_eq_true] at hchk; exact hchk.2)
    have hsL : s + nextD B x ≤ L := of_decide_eq_true hlen1
    have hlen : 2 * nextD B x ≤ x := of_decide_eq_true hlen2
    have hy : x + nextD B x = A + (s + nextD B x) := by omega
    have hbn : x + nextD B x ≤ 100000000 := by omega
    have hB' : (stepW M s B x (nextD B x) : Real) / 2 ^ 40
        ≤ Chebyshev.theta ((x + nextD B x : Nat) : Real) :=
      stepW_sound hM hA hL hx hsL (by omega : 10000 < x) hbn hlen hB
    obtain ⟨hcov, hacc⟩ := ih (s + nextD B x) (x + nextD B x) (stepW M s B x (nextD B x))
      X R hy hB' (Prod.ext hX (Prod.ext hR hrec))
    constructor
    · intro m hm1 hm2
      by_cases hlt : m + 1 ≤ x + nextD B x
      · have hbase := condA_bound hchk1
        have hmono : Chebyshev.theta (x : Real) ≤ Chebyshev.theta (m : Real) := by
          apply Chebyshev.theta_mono
          exact_mod_cast hm1
        have h1 : (1 : Real) ≤ (((m + 1 : Nat)) : Real) := by
          have : (0 : Real) ≤ ((m : Nat) : Real) := Nat.cast_nonneg m
          push_cast
          linarith
        have hle : (((m + 1 : Nat)) : Real) ≤ (((x + nextD B x : Nat)) : Real) := by
          exact_mod_cast hlt
        have hstep : (((m + 1 : Nat)) : Real) - 2 * Real.sqrt (((m + 1 : Nat)) : Real)
            ≤ ((x + nextD B x : Nat) : Real)
              - 2 * Real.sqrt (((x + nextD B x : Nat)) : Real) := by
          rcases lt_or_eq_of_le hle with hlt' | heq
          · exact le_of_lt (sqrt_step h1 hlt')
          · rw [heq]
        have hm1' : (((m : Nat)) : Real) + 1 = (((m + 1 : Nat)) : Real) := by push_cast; ring
        rw [hm1']
        linarith
      · have hge : x + nextD B x ≤ m := by omega
        exact hcov m hge (by omega)
    · exact hacc

/-- the shard interface for the adaptive chain -/
theorem chainD_shard {M A L N B X R : Nat} (hM : M = fCandidateMask divisors (A + 1) L)
    (hA : 10000 < A) (hL : A + L ≤ 100000000)
    (hB : (B : Real) / 2 ^ 40 ≤ Chebyshev.theta (A : Real))
    (hcert : chainD M L N 0 B A = (X, R, true)) :
    (∀ n : Nat, A ≤ n → n + 1 ≤ X →
        ((n : Real) + 1) - 2 * Real.sqrt ((n : Real) + 1) ≤ Chebyshev.theta (n : Real)) ∧
      (R : Real) / 2 ^ 40 ≤ Chebyshev.theta (X : Real) :=
  chainD_sound hM hA hL N 0 A B X R rfl hB hcert

end TFPFastMask

end TFPS1


open TFPS1
open TFPS1.TFPFastMask

set_option maxHeartbeats 0
set_option maxRecDepth 8000000

/-- shard 5: `theta` lower bound on `[3104574, 4678266]` plus the quantitative carry at `4678267` -/
theorem solution (hbase : (3411025892433723198 : Real) / 2 ^ 40 <= Chebyshev.theta (3104574 : Real)) (n : Nat) (h1 : 3104574 <= n) (h2 : n <= 4678266) :
    (((n : Real) + 1) - 2 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) ∧
      ((5140884555110703188 : Real) / 2 ^ 40 <= Chebyshev.theta (4678267 : Real)) := by
  have hcert : TFPS1.TFPFastMask.chainD
      (TFPS1.TFPFastMask.fCandidateMask TFPS1.RosserSieveData.divisors (3104574 + 1) 1573693)
      1573693 1452 0 3411025892433723198 3104574 = (4678267, 5140884555110703188, true) := by
    decide +kernel
  
  obtain ⟨hcov, hcarry⟩ :=
    TFPS1.TFPFastMask.chainD_shard rfl (by norm_num) (by norm_num) hbase hcert
  exact ⟨hcov n h1 (Nat.succ_le_succ h2), hcarry⟩
