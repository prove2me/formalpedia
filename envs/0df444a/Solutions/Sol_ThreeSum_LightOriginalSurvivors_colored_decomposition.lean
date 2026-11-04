-- Prove2me | solution 1 for ThreeSum.LightOriginalSurvivors.colored_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:08:02.491199+00:00
-- url     : https://prove2.me/submissions/d5ea58eb-0b5a-4307-8e41-da13d1b82d23

import Definitions.Def_Submission_ThreeSum_LightOriginalCollisionCleanup
import Definitions.Def_Submission_ThreeSum_LightOriginalSurvivors
import Theorems.Thm_ThreeSum_LightOriginalSurvivors_index_mem
import Theorems.Thm_ThreeSum_LightOriginalSurvivors_mem_iff
import Theorems.Thm_ThreeSum_LightOriginalCollisionCleanup_colored_decomposition


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightOriginalSurvivors
open LightOriginalBucketFilter LightOriginalCollisionCleanup
attribute [local instance] Classical.propDecidable
namespace ThreeSum.LightOriginalSurvivors
theorem _root_.solution (A B C : ℕ → ℤ) (keysB keysC : ℕ → ℕ) (nA nB nC : ℕ) :
    (∃ i < nA, ∃ j < nB, ∃ k < nC, C k = A i + B j) ↔
      LightDeletedTwoSum.Hit (badIndex keysB nB) B A C nC nA (badIndices keysB nB).length 1 ∨
      LightDeletedTwoSum.Hit (badIndex keysC nC) C A B nB nA (badIndices keysC nC).length (-1) ∨
      ∃ i < nA, ∃ j < (indices keysB nB).length, ∃ k < (indices keysC nC).length,
        C (index keysC nC k) = A i + B (index keysB nB j) := by
  rw [LightOriginalCollisionCleanup.colored_decomposition]
  constructor
  · rintro (h | h | ⟨i,hi,j,hj,k,hk,he⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · obtain ⟨jj,hjj,rfl⟩ := (mem_iff keysB nB j).mp hj
      obtain ⟨kk,hkk,rfl⟩ := (mem_iff keysC nC k).mp hk
      exact Or.inr (Or.inr ⟨i,hi,jj,hjj,kk,hkk,he⟩)
  · rintro (h | h | ⟨i,hi,j,hj,k,hk,he⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨i,hi,_,index_mem hj,_,index_mem hk,he⟩)
end ThreeSum.LightOriginalSurvivors
