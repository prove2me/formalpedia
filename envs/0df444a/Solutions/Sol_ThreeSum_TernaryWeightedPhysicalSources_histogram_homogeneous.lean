-- Prove2me | solution 1 for ThreeSum.TernaryWeightedPhysicalSources.histogram_homogeneous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:58:54.33658+00:00
-- url     : https://prove2.me/submissions/f8c85dfb-923c-45bc-8d7c-e9e8f39fa790

import Definitions.Def_Submission_ThreeSum_TernaryPhysicalSources
import Definitions.Def_Submission_ThreeSum_LightTernaryWeightedHistogram
import Definitions.Def_Submission_ThreeSum_TernaryWeightedPhysicalSources
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_ThreeSum_LightTernaryWeightedHistogram_total_zero
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.LightTernaryWeightedHistogram.total_zero
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryWeightedPhysicalSources
open Finset TernaryJointType TernaryBank TernaryConvolution
open scoped BigOperators
variable {ι κ : Type*}
namespace ThreeSum.TernaryWeightedPhysicalSources
theorem _root_.solution {N h : ℕ} (S : Finset ι)
    (word : ι → TritWord N) (weight : ι → ℤ)
    (hrank : ∀ i ∈ S, rank (word i)=h) :
    ∀ A, histogram S word weight A≠0 → rank A=h := by
  classical
  intro A hA
  by_contra hneq
  apply hA
  unfold histogram
  apply sum_eq_zero
  intro i hi
  have hn : word i≠A := by
    intro he
    exact hneq (by rw [← he]; exact hrank i hi)
  simp [hn]
end ThreeSum.TernaryWeightedPhysicalSources
