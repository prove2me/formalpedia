-- Prove2me | solution 1 for ThreeSum.TernaryPhysicalSources.rank_of_type
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:37:39.371339+00:00
-- url     : https://prove2.me/submissions/fa0d42c0-86d9-4ec9-b572-ae0b7da92b5b

import Definitions.Def_Submission_ThreeSum_TernaryConvolution
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalSources
import Theorems.Thm_ThreeSum_TernaryPhysicalSources_rank_eq_type_sum
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
namespace ThreeSum.TernaryPhysicalSources
theorem _root_.solution {N : ℕ} {R : TritWord N} {α : DigitType}
    (h : HasType R α) : rank R=α 1+2*α 2 := by
  change ∀ d, digitCount R d = α d at h
  rw [rank_eq_type_sum]
  simp only [h]
  simp [Fin.sum_univ_succ]
end ThreeSum.TernaryPhysicalSources
