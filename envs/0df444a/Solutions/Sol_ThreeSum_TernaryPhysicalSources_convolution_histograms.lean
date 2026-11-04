-- Prove2me | solution 1 for ThreeSum.TernaryPhysicalSources.convolution_histograms
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:37:41.481267+00:00
-- url     : https://prove2.me/submissions/13994b37-3bd9-42e5-95a3-b1e52849568b

import Definitions.Def_Submission_ThreeSum_TernaryConvolution
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalSources
import Theorems.Thm_ThreeSum_TernaryPhysicalSources_histogram_sum
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords



set_option autoImplicit false
open ThreeSum ThreeSum.TernaryPhysicalSources
open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryConvolution
variable {ι κ : Type*}
namespace ThreeSum.TernaryPhysicalSources
theorem _root_.solution {N : ℕ} (S : Finset ι) (T : Finset κ)
    (left : ι → TritWord N) (right : κ → TritWord N) (Q : TritWord N) :
    convolution (histogram S left) (histogram T right) Q=pairCount S T left right Q := by
  classical
  have hcon : convolution (histogram S left) (histogram T right) Q =
      ∑ A, histogram S left A *
        (∑ B, histogram T right B*(if Adds A B Q then 1 else 0)) := by
    unfold convolution
    apply Finset.sum_congr rfl
    intro A hA
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro B hB
    split <;> simp_all
  rw [hcon]
  simp_rw [histogram_sum]
  rfl
end ThreeSum.TernaryPhysicalSources
