-- Prove2me | solution 1 for ThreeSum.TernaryBankEnumeration.words_image_bank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:10:36.929264+00:00
-- url     : https://prove2.me/submissions/10a5f858-41e0-45ef-acdb-53bf034e857c

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_sum
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_mem_words
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_fromList
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_words
attribute [local simp] ThreeSum.TernaryAddresses.codes_length
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits


attribute [local simp] ThreeSum.TernaryBankEnumeration.wordList_length
attribute [local simp] ThreeSum.TernaryBankEnumeration.wordList_sum

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryBankEnumeration
open ThreeSum.TernaryEnumeration ThreeSum.TernaryAddresses
open ThreeSum.TernaryJointType ThreeSum.TernaryBank
namespace ThreeSum.TernaryBankEnumeration
theorem _root_.solution (N T : ℕ) :
    (words N T).toFinset = (bank N T).image wordList := by
  ext xs
  constructor
  · intro hx
    have hx' := List.mem_toFinset.mp hx
    obtain ⟨hlen, hdigits, hsum⟩ := (mem_words N T xs).mp hx'
    let w := fromList xs hlen hdigits
    have hlist : wordList w = xs := wordList_fromList xs hlen hdigits
    apply Finset.mem_image.mpr
    refine ⟨w, ?_, hlist⟩
    apply (wordList_mem_words w).mp
    simpa only [hlist] using hx'
  · intro hx
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
    exact List.mem_toFinset.mpr ((wordList_mem_words w).mpr hw)
end ThreeSum.TernaryBankEnumeration
