-- Prove2me | solution 1 for ThreeSum.LightNaturalDot.dot_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:36:07.556857+00:00
-- url     : https://prove2.me/submissions/013639b3-eaa6-4022-944f-9a88450c5650

import Definitions.Def_Submission_ThreeSum_LightBooleanDot
import Definitions.Def_Submission_ThreeSum_LightRadixDigit
import Definitions.Def_Submission_ThreeSum_LightNaturalDot
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
open ThreeSum ThreeSum.LightNaturalDot
open Light Finset
open scoped BigOperators
namespace ThreeSum.LightNaturalDot
theorem _root_.solution (f g : ℕ → ℕ) {n j U V : ℕ}
    (hf : ∀ i<n, f i≤U) (hg : ∀ i<n, g i≤V) (hj : j≤n) :
    dot f g j≤j*(U*V) := by
  unfold dot LightBooleanDot.dot
  calc
    ∑ i ∈ range j, f i*g i≤∑ _i ∈ range j, U*V := by
      apply sum_le_sum
      intro i hi
      have hin := (mem_range.mp hi).trans_le hj
      exact Nat.mul_le_mul (hf i hin) (hg i hin)
    _ = _ := by simp
end ThreeSum.LightNaturalDot
