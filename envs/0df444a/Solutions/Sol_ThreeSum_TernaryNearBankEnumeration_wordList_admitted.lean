-- Prove2me | solution 1 for ThreeSum.TernaryNearBankEnumeration.wordList_admitted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:10:38.096258+00:00
-- url     : https://prove2.me/submissions/1ce9d3e3-4448-4b65-b0bb-13c7ad04d811

import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Mathlib.Data.List.Forall2
import Definitions.Def_Submission_ThreeSum_TernaryNearBankEnumeration
import Theorems.Thm_P2M_ThreeSum_TernaryNearBankEnumeration_wordList_forall__77ed6a00ca9b
import Theorems.Thm_ThreeSum_TernaryNearBankEnumeration_wordList_deficit
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_admitted_iff
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords



set_option autoImplicit false
open ThreeSum ThreeSum.TernaryNearBankEnumeration
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryBankEnumeration
namespace ThreeSum.TernaryNearBankEnumeration
theorem _root_.solution {N D : ℕ} (Q R : TritWord N) :
    TernaryNearEnumeration.Admitted (wordList Q) (wordList R) D ↔
      R ∈ nearWords Q D := by
  rw [TernaryNearEnumeration.admitted_iff,wordList_forall₂,wordList_deficit,mem_nearWords]
end ThreeSum.TernaryNearBankEnumeration
