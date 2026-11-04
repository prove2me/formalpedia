-- Prove2me | solution 1 for ThreeSum.TernaryPhysicalSources.histogram_homogeneous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:37:40.42614+00:00
-- url     : https://prove2.me/submissions/5b976bcf-88e0-4e51-af51-f9e930daa51d

import Definitions.Def_Submission_ThreeSum_TernaryConvolution
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalSources
import Theorems.Thm_ThreeSum_TernaryPhysicalSources_histogram_nonneg
import Theorems.Thm_ThreeSum_TernaryPhysicalSources_histogram_pos_iff
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
theorem _root_.solution {N h : ℕ} (S : Finset ι) (word : ι → TritWord N)
    (hrank : ∀ i ∈ S, rank (word i)=h) :
    ∀ A, histogram S word A≠0 → rank A=h := by
  intro A hA
  have hp : 0 < histogram S word A := lt_of_le_of_ne (histogram_nonneg S word A) (Ne.symm hA)
  obtain ⟨i,hi,he⟩ := (histogram_pos_iff S word A).mp hp
  simpa only [he] using hrank i hi
end ThreeSum.TernaryPhysicalSources
