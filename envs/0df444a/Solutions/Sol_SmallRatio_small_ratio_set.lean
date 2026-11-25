-- Prove2me | solution 1 for SmallRatio.small_ratio_set
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:44:07.661796+00:00
-- url     : https://prove2.me/submissions/f91e1161-90e8-4dce-9e71-bfcb85c1597e

module
public import Definitions.Def_SmallRatio_Main
public import Definitions.Def_SmallRatio_Subgroup
public import Theorems.Thm_SmallRatio_dedekindSum_zero_left
public import Theorems.Thm_SmallRatio_smallRatioSum_zero
public import Theorems.Thm_SmallRatio_sum_smallRatioSum
public import Theorems.Thm_SmallRatio_den_one
public import Theorems.Thm_SmallRatio_den_zero
public import Theorems.Thm_SmallRatio_rem_one
public import Theorems.Thm_SmallRatio_rem_zero
public import Theorems.Thm_SmallRatio_small_ratio_element
attribute [local simp] SmallRatio.den_one
attribute [local simp] SmallRatio.den_zero
attribute [local simp] SmallRatio.rem_one
attribute [local simp] SmallRatio.rem_zero



set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {p : ℕ}
namespace SmallRatio
theorem _root_.solution (hp : p.Prime) (H : Finset (ZMod p)) :
    |12 * ∑ x ∈ H, dedekindSum x.val p - p * subgroupSmallRatio p H| ≤
      H.card * (12 * Nat.log 2 p + 6) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← sum_smallRatioSum hp, mul_sum, mul_sum, ← sum_sub_distrib]
  calc |∑ x ∈ H, (12 * dedekindSum x.val p - p * smallRatioSum p x.val)|
      ≤ ∑ x ∈ H, |12 * dedekindSum x.val p - p * smallRatioSum p x.val| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x ∈ H, ((12 * Nat.log 2 p + 6 : ℕ) : ℚ) := by
        apply sum_le_sum
        intro x _
        by_cases hx : x = 0
        · subst hx
          rw [ZMod.val_zero, dedekindSum_zero_left, smallRatioSum_zero hp]
          simp only [mul_zero, sub_zero, abs_zero]
          positivity
        · have h1 := small_ratio_element hp (Nat.pos_of_ne_zero ((ZMod.val_ne_zero x).2 hx))
            (ZMod.val_lt x)
          push_cast; exact h1
    _ = H.card * (12 * Nat.log 2 p + 6) := by
        rw [sum_const, nsmul_eq_mul]; push_cast; ring
end SmallRatio
