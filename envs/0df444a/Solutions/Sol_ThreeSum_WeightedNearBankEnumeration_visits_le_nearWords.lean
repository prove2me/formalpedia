-- Prove2me | solution 1 for ThreeSum.WeightedNearBankEnumeration.visits_le_nearWords
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:22:25.765479+00:00
-- url     : https://prove2.me/submissions/50346517-ad75-470e-a4ba-bf872041c02e

import Definitions.Def_Submission_Weighted_NearEnumeration
import Definitions.Def_Submission_Weighted_BankEnumeration
import Mathlib.Data.List.Forall2
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Theorems.Thm_ThreeSum_WeightedNearBankEnumeration_mem_nearWords
import Theorems.Thm_ThreeSum_WeightedNearBankEnumeration_codes_length_eq_nearWords_card
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryAddresses_visits_le_codes
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_WeightedAddresses_codes_length
import Theorems.Thm_ThreeSum_WeightedAddresses_visits_le_codes
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_mem_bank
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_cost
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_one
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_two
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_zero
import Theorems.Thm_ThreeSum_WeightedEnumeration_mem_digits
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_codes_length
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_mem_digits
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_visits_le_codes
attribute [local simp] ThreeSum.TernaryAddresses.codes_length
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits
attribute [local simp] ThreeSum.WeightedAddresses.codes_length
attribute [local simp] ThreeSum.WeightedBankEnumeration.mem_bank
attribute [local simp] ThreeSum.WeightedBankEnumeration.wordList_cost
attribute [local simp] ThreeSum.WeightedBankEnumeration.wordList_length
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_one
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_two
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_zero
attribute [local simp] ThreeSum.WeightedEnumeration.mem_digits
attribute [local simp] ThreeSum.WeightedNearEnumeration.codes_length
attribute [local simp] ThreeSum.WeightedNearEnumeration.mem_digits


attribute [local simp] ThreeSum.WeightedNearBankEnumeration.mem_nearWords

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedNearBankEnumeration
open ThreeSum.TernaryJointType ThreeSum.WeightedBankEnumeration
open WeightedCache (Below)
open ThreeSum.WeightedEnumeration (digitCost)
namespace ThreeSum.WeightedNearBankEnumeration
theorem _root_.solution {N : ℕ} (Q : TritWord N) (D : ℕ) :
    WeightedNearEnumeration.visits (wordList Q) D ≤ (N+1)*(nearWords Q D).card := by
  have h := WeightedNearEnumeration.visits_le_codes (wordList Q) D
  simpa only [wordList_length,codes_length_eq_nearWords_card] using h
end ThreeSum.WeightedNearBankEnumeration
