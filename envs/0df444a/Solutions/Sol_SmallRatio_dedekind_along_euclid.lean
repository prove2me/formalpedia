-- Prove2me | solution 1 for SmallRatio.dedekind_along_euclid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:38:45.867802+00:00
-- url     : https://prove2.me/submissions/408f9107-bc3d-40e7-b11f-0c71981a97cd

module
public import Definitions.Def_SmallRatio_Reciprocity
public import Definitions.Def_SmallRatio_Euclid
public import Definitions.Def_SmallRatio_AlongEuclid
public import Theorems.Thm_SmallRatio_twelve_s_eq_sum
public import Theorems.Thm_SmallRatio_recipTerm_eq
public import Theorems.Thm_SmallRatio_err_bound

set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {k h : ℕ} (hh : 0 < h) (hhk : h < k) (hc : Nat.Coprime k h)
include hh hhk hc
namespace SmallRatio
theorem _root_.solution :
    |12 * dedekindSum h k - ∑ i ∈ Icc 1 (steps k h),
        (-1) ^ (i + 1) * ((k : ℚ) / ((rem k h i : ℚ) * den k h i))| ≤ 4 * steps k h := by
  rw [twelve_s_eq_sum hh hhk hc, ← sum_sub_distrib]
  calc |∑ i ∈ Icc 1 (steps k h), ((-1) ^ (i + 1) * recipTerm k h i -
          (-1) ^ (i + 1) * ((k : ℚ) / ((rem k h i : ℚ) * den k h i)))|
      ≤ ∑ i ∈ Icc 1 (steps k h), |(-1) ^ (i + 1) * recipTerm k h i -
          (-1) ^ (i + 1) * ((k : ℚ) / ((rem k h i : ℚ) * den k h i))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Icc 1 (steps k h), (4 : ℚ) := by
        apply sum_le_sum
        intro i hi
        rw [mem_Icc] at hi
        rw [recipTerm_eq hh hhk hc hi.1 hi.2, ← mul_sub, abs_mul, abs_pow, abs_neg, abs_one,
          one_pow, one_mul, add_sub_cancel_left]
        exact err_bound hh hhk hc hi.1 hi.2
    _ = 4 * steps k h := by
        rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring
end SmallRatio
