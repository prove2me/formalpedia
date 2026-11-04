-- Prove2me | solution 1 for ThreeSum.LightTernaryWeightedHistogram.total_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:58:53.26181+00:00
-- url     : https://prove2.me/submissions/73986a2a-a23a-4134-ba04-bbb0de5fd148

import Definitions.Def_Submission_ThreeSum_LightHistogram
import Definitions.Def_Submission_ThreeSum_LightTernaryWeightedHistogram
import Theorems.Thm_ThreeSum_LightTernaryWeightedHistogram_total_zero
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_List_abs_sum_le_sum_abs
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LightHistogram.count_zero


attribute [local simp] ThreeSum.LightTernaryWeightedHistogram.total_zero

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryWeightedHistogram
open Light Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
namespace ThreeSum.LightTernaryWeightedHistogram
theorem _root_.solution (key : ℕ → ℕ) (weight : ℕ → ℤ) (r n U : ℕ)
    (h : ∀ i < n, |weight i| ≤ U) : |total key weight r n| ≤ (n : ℤ)*U := by
  unfold total
  calc
    _ ≤ ∑ i ∈ range n, |if key i=r then weight i else 0| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ range n, (U : ℤ) := by
      apply sum_le_sum
      intro i hi
      split_ifs
      · exact h i (mem_range.mp hi)
      · simp
    _ = (n : ℤ)*U := by simp
end ThreeSum.LightTernaryWeightedHistogram
