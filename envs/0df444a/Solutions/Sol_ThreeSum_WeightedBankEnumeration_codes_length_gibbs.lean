-- Prove2me | solution 1 for ThreeSum.WeightedBankEnumeration.codes_length_gibbs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:15:56.904771+00:00
-- url     : https://prove2.me/submissions/d7762e7d-19f2-4216-865c-51cb4f47b61d

import Definitions.Def_Submission_Weighted_Addresses
import Definitions.Def_Submission_Weighted_Cache
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_Weighted_BankEnumeration
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_mem_bank
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_cost
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_codes_length_eq_bank_card
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryBank_bank_card_gibbs
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_WeightedAddresses_codes_length
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_one
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_two
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_zero
import Theorems.Thm_ThreeSum_WeightedEnumeration_mem_digits
import Theorems.Thm_WeightedCache_bank_card_gibbs
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
theorem _root_.solution (N T : ℕ) (y : ℝ) (hy : 0≤y) (hy1 : y≤1) :
    (codes N T).length*y^T ≤ (1+y^512+y^1025)^N := by
  rw [codes_length_eq_bank_card]
  have hh := WeightedCache.bank_card_gibbs N ![0,512,1025] T y hy hy1
  simpa [bank,Fin.sum_univ_succ,add_assoc] using hh
end ThreeSum.WeightedBankEnumeration
