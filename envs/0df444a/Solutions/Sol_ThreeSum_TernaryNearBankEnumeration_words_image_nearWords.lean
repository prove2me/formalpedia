-- Prove2me | solution 1 for ThreeSum.TernaryNearBankEnumeration.words_image_nearWords
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:12:45.110138+00:00
-- url     : https://prove2.me/submissions/f43e9567-9f77-4c86-b15b-171fbbc10024

import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Mathlib.Data.List.Forall2
import Definitions.Def_Submission_ThreeSum_TernaryNearBankEnumeration
import Theorems.Thm_ThreeSum_TernaryNearBankEnumeration_wordList_admitted
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_digits
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_fromList
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_sum
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_words
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_admitted_digits
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_admitted_length
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_codes_length
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_words
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
theorem _root_.solution {N : ℕ} (Q : TritWord N) (D : ℕ) :
    (TernaryNearEnumeration.words (wordList Q) D).toFinset =
      (nearWords Q D).image wordList := by
  ext rs
  constructor
  · intro hrs
    have hrs' := List.mem_toFinset.mp hrs
    have had := (TernaryNearEnumeration.mem_words _ _ _).mp hrs'
    have hlen : rs.length=N := (TernaryNearEnumeration.admitted_length had).trans (wordList_length Q)
    have hdigits := TernaryNearEnumeration.admitted_digits (wordList_digits Q) had
    let R := fromList rs hlen hdigits
    have hlist : wordList R=rs := wordList_fromList rs hlen hdigits
    refine Finset.mem_image.mpr ⟨R,?_,hlist⟩
    apply (wordList_admitted Q R).mp
    simpa only [hlist] using had
  · intro hrs
    obtain ⟨R,hR,rfl⟩ := Finset.mem_image.mp hrs
    exact List.mem_toFinset.mpr ((TernaryNearEnumeration.mem_words _ _ _).mpr
      ((wordList_admitted Q R).mpr hR))
end ThreeSum.TernaryNearBankEnumeration
