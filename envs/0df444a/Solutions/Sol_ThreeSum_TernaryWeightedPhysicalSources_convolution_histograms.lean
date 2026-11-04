-- Prove2me | solution 1 for ThreeSum.TernaryWeightedPhysicalSources.convolution_histograms
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:28:18.600594+00:00
-- url     : https://prove2.me/submissions/3401e349-6474-4ec5-9d55-0f6bf6b644b4

import Definitions.Def_Submission_ThreeSum_TernaryPhysicalSources
import Definitions.Def_Submission_ThreeSum_LightTernaryWeightedHistogram
import Definitions.Def_Submission_ThreeSum_TernaryWeightedPhysicalSources
import Theorems.Thm_ThreeSum_TernaryWeightedPhysicalSources_histogram_sum
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
import Theorems.Thm_ThreeSum_TernaryPhysicalSources_histogram_sum
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
theorem _root_.solution {N : ℕ} (S : Finset ι) (T : Finset κ)
    (left : ι → TritWord N) (right : κ → TritWord N)
    (leftWeight : ι → ℤ) (rightWeight : κ → ℤ) (Q : TritWord N) :
    convolution (histogram S left leftWeight) (histogram T right rightWeight) Q=
      pairWeight S T left right leftWeight rightWeight Q := by
  classical
  have hcon : convolution (histogram S left leftWeight)
      (histogram T right rightWeight) Q=
      ∑ A, histogram S left leftWeight A*
        (∑ B, histogram T right rightWeight B*(if Adds A B Q then 1 else 0)) := by
    unfold convolution
    apply sum_congr rfl
    intro A hA
    rw [mul_sum]
    apply sum_congr rfl
    intro B hB
    split <;> simp_all
  rw [hcon,histogram_sum]
  unfold pairWeight
  apply sum_congr rfl
  intro i hi
  rw [histogram_sum,mul_sum]
  apply sum_congr rfl
  intro j hj
  split <;> simp_all
end ThreeSum.TernaryWeightedPhysicalSources
