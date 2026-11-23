-- Prove2me | solution 1 for SumProduct.zeta_pow_apply_prime_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:01:53.401698+00:00
-- url     : https://prove2.me/submissions/95a202ff-40c4-49d7-af5e-86242fdc1366

import Mathlib
import Definitions.Def_SumProduct_EulerBound

set_option autoImplicit true
open scoped NumberField
open NumberField UniqueFactorizationMonoid
open SumProduct
variable {K : Type*} [Field K] [NumberField K]
open scoped ArithmeticFunction.zeta
namespace SumProduct
theorem _root_.solution {p : ℕ} (hp : p.Prime) (d k : ℕ) :
    (ζ ^ d : ArithmeticFunction ℕ) (p ^ k) = Nat.multichoose d k := by
  induction d generalizing k with
  | zero =>
    rw [pow_zero, ArithmeticFunction.one_apply]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · rw [if_neg (fun h => by simp [hp.ne_one, hk.ne'] at h),
        Nat.multichoose_eq, Nat.choose_eq_zero_of_lt (by omega)]
  | succ d ih =>
    rw [pow_succ, ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (fun a b => (ζ ^ d : ArithmeticFunction ℕ) a * ζ b),
      Nat.sum_divisors_prime_pow hp]
    have hz : ∀ i ∈ Finset.range (k + 1),
        (ζ ^ d : ArithmeticFunction ℕ) (p ^ i) * ζ (p ^ k / p ^ i) = Nat.multichoose d i := by
      intro i hi
      rw [Finset.mem_range, Nat.lt_succ_iff] at hi
      rw [ih i, Nat.pow_div hi hp.pos,
        ArithmeticFunction.zeta_apply_ne (pow_ne_zero (k - i) hp.pos.ne'), mul_one]
    rw [Finset.sum_congr rfl hz]
    rw [Nat.sum_range_multichoose, Nat.multichoose_eq, show d + 1 + k - 1 = k + d by omega,
      ← Nat.choose_symm (Nat.le_add_right k d), Nat.add_sub_cancel_left]
end SumProduct
