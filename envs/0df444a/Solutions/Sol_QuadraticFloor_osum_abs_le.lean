-- Prove2me | solution 1 for QuadraticFloor.osum_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:00:05.239003+00:00
-- url     : https://prove2.me/submissions/ce72f333-f16b-4401-a0c8-d155a48e86f8

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_Monic

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
namespace QuadraticFloor
theorem _root_.solution (t : ℤ) (g : ℤ → ℤ) (hg : ∀ j, |g j| ≤ 1) : |osum t g| ≤ |t| := by
  unfold osum
  split_ifs with h
  · calc |∑ j ∈ Ico 0 t, g j| ≤ ∑ j ∈ Ico 0 t, |g j| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Ico 0 t, (1 : ℤ) := sum_le_sum fun j _ => hg j
      _ = |t| := by
        rw [sum_const, Int.card_Ico, nsmul_eq_mul, mul_one, abs_of_nonneg h, sub_zero,
          Int.toNat_of_nonneg h]
  · rw [abs_neg]
    calc |∑ j ∈ Ico t 0, g j| ≤ ∑ j ∈ Ico t 0, |g j| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Ico t 0, (1 : ℤ) := sum_le_sum fun j _ => hg j
      _ = |t| := by
        rw [sum_const, Int.card_Ico, nsmul_eq_mul, mul_one, abs_of_neg (by omega), zero_sub,
          Int.toNat_of_nonneg (by omega)]
end QuadraticFloor
