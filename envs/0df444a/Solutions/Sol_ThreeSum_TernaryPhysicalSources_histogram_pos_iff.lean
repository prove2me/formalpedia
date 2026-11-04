-- Prove2me | solution 1 for ThreeSum.TernaryPhysicalSources.histogram_pos_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:36:43.74383+00:00
-- url     : https://prove2.me/submissions/92b13fff-a312-46af-825f-a1b242e75f0c

import Definitions.Def_Submission_ThreeSum_TernaryConvolution
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalSources
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
theorem _root_.solution {N : ℕ} (S : Finset ι) (word : ι → TritWord N) (A : TritWord N) :
    0 < histogram S word A ↔ ∃ i ∈ S, word i=A := by
  unfold histogram
  rw [Finset.sum_pos_iff_of_nonneg (by intro i hi; split <;> norm_num)]
  constructor
  · rintro ⟨i,hi,hpos⟩
    have he : word i=A := by
      by_contra hn
      simp only [if_neg hn] at hpos
      omega
    exact ⟨i,hi,he⟩
  · rintro ⟨i,hi,he⟩
    exact ⟨i,hi,by simp only [if_pos he]; norm_num⟩
end ThreeSum.TernaryPhysicalSources
