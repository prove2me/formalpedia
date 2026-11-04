-- Prove2me | solution 1 for ThreeSum.LightTernaryWeightedSum.sum_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:41:12.799407+00:00
-- url     : https://prove2.me/submissions/9fa4d3d2-3b89-40a4-bc5f-1a91410d5592

import Definitions.Def_Submission_ThreeSum_LightLookupSum
import Definitions.Def_Submission_ThreeSum_LightTernaryWeightedSum
import Theorems.Thm_ThreeSum_LightTernaryWeightedSum_sum_zero
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_List_abs_sum_le_sum_abs
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast


attribute [local simp] ThreeSum.LightTernaryWeightedSum.sum_zero

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryWeightedSum
open Light Finset
namespace ThreeSum.LightTernaryWeightedSum
theorem _root_.solution (weights keys : ℕ → ℕ) (f : ℕ → ℤ) {n j U : ℕ}
    (hw : ∀ i < n, weights i ≤ 2) (hf : ∀ i < n, |f (keys i)| ≤ U)
    (hj : j ≤ n) : |sum weights keys f j| ≤ 2*j*(U : ℤ) := by
  unfold sum
  calc
    |∑ i ∈ range j, (weights i : ℤ)*f (keys i)| ≤
        ∑ i ∈ range j, |(weights i : ℤ)*f (keys i)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ range j, 2*(U : ℤ) := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i < n := (mem_range.mp hi).trans_le hj
      rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg _)]
      exact mul_le_mul (by exact_mod_cast hw i hin) (hf i hin) (abs_nonneg _)
        (by norm_num)
    _ = _ := by simp; ring
end ThreeSum.LightTernaryWeightedSum
