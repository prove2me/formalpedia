-- Prove2me | solution 1 for P2M_ThreeSum_TernaryNearBankEnumeration_wordList_forall__77ed6a00ca9b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:08:32.110233+00:00
-- url     : https://prove2.me/submissions/744ba09b-7dfa-4c8e-9f50-7bb0d8b645fe

import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Mathlib.Data.List.Forall2
import Definitions.Def_Submission_ThreeSum_TernaryNearBankEnumeration
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_sum
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_codes_length
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_digits
attribute [local simp] ThreeSum.TernaryAddresses.codes_length
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
attribute [local simp] ThreeSum.TernaryBankEnumeration.wordList_length
attribute [local simp] ThreeSum.TernaryBankEnumeration.wordList_sum
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits
attribute [local simp] ThreeSum.TernaryNearEnumeration.codes_length
attribute [local simp] ThreeSum.TernaryNearEnumeration.mem_digits



set_option autoImplicit false
open ThreeSum ThreeSum.TernaryNearBankEnumeration
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryBankEnumeration
namespace ThreeSum.TernaryNearBankEnumeration
theorem _root_.solution {N : ℕ} (R Q : TritWord N) :
    List.Forall₂ (· ≤ ·) (wordList R) (wordList Q) ↔ Below R Q := by
  rw [List.forall₂_iff_get]
  constructor
  · rintro ⟨_,h⟩ i
    have hiR : i.val < (wordList R).length := by simp [i.isLt]
    have hiQ : i.val < (wordList Q).length := by simp [i.isLt]
    have hh := h i.val hiR hiQ
    simpa [wordList,List.get_eq_getElem] using hh
  · intro h
    refine ⟨by simp,?_⟩
    intro i hiR hiQ
    have hi : i < N := by simpa using hiR
    simpa [wordList,List.get_eq_getElem] using h ⟨i,hi⟩
end ThreeSum.TernaryNearBankEnumeration
