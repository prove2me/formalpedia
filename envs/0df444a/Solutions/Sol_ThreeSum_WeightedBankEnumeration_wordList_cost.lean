-- Prove2me | solution 1 for ThreeSum.WeightedBankEnumeration.wordList_cost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:08:19.42614+00:00
-- url     : https://prove2.me/submissions/8ea6e33e-7f7f-46d1-95f6-a2db2645596c

import Definitions.Def_Submission_Weighted_Addresses
import Definitions.Def_Submission_Weighted_Cache
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_Weighted_BankEnumeration
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_mem_bank
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_digitCost_eq
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_WeightedAddresses_codes_length
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_one
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_two
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_zero
import Theorems.Thm_ThreeSum_WeightedEnumeration_mem_digits
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

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedBankEnumeration
open ThreeSum.WeightedEnumeration ThreeSum.WeightedAddresses
open ThreeSum.TernaryJointType
namespace ThreeSum.WeightedBankEnumeration
theorem _root_.solution {N : ℕ} (w : TritWord N) :
    ((wordList w).map digitCost).sum = cacheCost w := by
  simp [wordList,cacheCost,WeightedCache.cost,List.sum_ofFn,digitCost_eq]
end ThreeSum.WeightedBankEnumeration
