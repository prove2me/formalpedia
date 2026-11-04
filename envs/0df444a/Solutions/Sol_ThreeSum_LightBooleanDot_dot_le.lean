-- Prove2me | solution 1 for ThreeSum.LightBooleanDot.dot_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:26:18.190374+00:00
-- url     : https://prove2.me/submissions/704ab79a-2b05-4189-a018-79e4cc3895b9

import Definitions.Def_Submission_ThreeSum_LightArray
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_Submission_ThreeSum_LightBooleanDot
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast



set_option autoImplicit false
open ThreeSum ThreeSum.LightBooleanDot
open Light Finset
open scoped BigOperators
namespace ThreeSum.LightBooleanDot
theorem _root_.solution (f g : ℕ → ℕ) {n j : ℕ}
    (hf : ∀ i < n, f i ≤ 1) (hg : ∀ i < n, g i ≤ 1) (hj : j ≤ n) :
    dot f g j ≤ j := by
  unfold dot
  calc
    _ ≤ ∑ _i ∈ range j, 1 := by
      apply sum_le_sum
      intro i hi
      have hin : i < n := (mem_range.mp hi).trans_le hj
      exact (Nat.mul_le_mul (hf i hin) (hg i hin)).trans (by decide)
    _ = j := by simp
end ThreeSum.LightBooleanDot
