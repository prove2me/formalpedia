-- Prove2me | solution 1 for ThreeSum.TernaryPhysicalSources.pairCount_pos_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:36:57.562756+00:00
-- url     : https://prove2.me/submissions/841b96f7-d7a6-4950-aa75-aeb5027d20d2

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
theorem _root_.solution {N : ℕ} (S : Finset ι) (T : Finset κ)
    (left : ι → TritWord N) (right : κ → TritWord N) (Q : TritWord N) :
    0 < pairCount S T left right Q ↔
      ∃ i ∈ S, ∃ j ∈ T, Adds (left i) (right j) Q := by
  unfold pairCount
  rw [Finset.sum_pos_iff_of_nonneg (by
    intro i hi
    apply Finset.sum_nonneg
    intro j hj
    split <;> norm_num)]
  constructor
  · rintro ⟨i,hi,hpos⟩
    rw [Finset.sum_pos_iff_of_nonneg (by intro j hj; split <;> norm_num)] at hpos
    obtain ⟨j,hj,hp⟩ := hpos
    have ha : Adds (left i) (right j) Q := by
      by_contra hn
      simp only [if_neg hn] at hp
      omega
    exact ⟨i,hi,j,hj,ha⟩
  · rintro ⟨i,hi,j,hj,ha⟩
    refine ⟨i,hi,?_⟩
    rw [Finset.sum_pos_iff_of_nonneg (by intro j hj; split <;> norm_num)]
    exact ⟨j,hj,by simp only [if_pos ha]; norm_num⟩
end ThreeSum.TernaryPhysicalSources
