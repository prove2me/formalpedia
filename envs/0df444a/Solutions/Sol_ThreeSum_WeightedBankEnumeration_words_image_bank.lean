-- Prove2me | solution 1 for ThreeSum.WeightedBankEnumeration.words_image_bank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:12:39.344803+00:00
-- url     : https://prove2.me/submissions/5e197f5a-5620-49ba-a4d8-4d849705c3d3

import Definitions.Def_Submission_Weighted_Addresses
import Definitions.Def_Submission_Weighted_Cache
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_Weighted_BankEnumeration
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_mem_bank
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_cost
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_mem_words
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_fromList
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_words
import Theorems.Thm_ThreeSum_WeightedAddresses_codes_length
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_one
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_two
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_zero
import Theorems.Thm_ThreeSum_WeightedEnumeration_mem_digits
import Theorems.Thm_ThreeSum_WeightedEnumeration_mem_words
attribute [local simp] ThreeSum.TernaryAddresses.codes_length
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits
attribute [local simp] ThreeSum.WeightedAddresses.codes_length
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_one
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_two
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_zero
attribute [local simp] ThreeSum.WeightedEnumeration.mem_digits


attribute [local simp] ThreeSum.WeightedBankEnumeration.mem_bank
attribute [local simp] ThreeSum.WeightedBankEnumeration.wordList_length
attribute [local simp] ThreeSum.WeightedBankEnumeration.wordList_cost

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedBankEnumeration
open ThreeSum.WeightedEnumeration ThreeSum.WeightedAddresses
open ThreeSum.TernaryJointType
namespace ThreeSum.WeightedBankEnumeration
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
end ThreeSum.WeightedBankEnumeration
