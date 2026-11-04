-- Prove2me | solution 1 for ThreeSum.WeightedNearBankEnumeration.codes_length_gibbs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:22:26.831718+00:00
-- url     : https://prove2.me/submissions/7ce44c2e-7b1f-49bb-ab53-730359150243

import Definitions.Def_Submission_Weighted_NearEnumeration
import Definitions.Def_Submission_Weighted_BankEnumeration
import Mathlib.Data.List.Forall2
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Theorems.Thm_ThreeSum_WeightedNearBankEnumeration_mem_nearWords
import Theorems.Thm_ThreeSum_WeightedNearBankEnumeration_codes_length_eq_nearWords_card
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_WeightedAddresses_codes_length
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_mem_bank
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_cost
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_one
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_two
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_zero
import Theorems.Thm_ThreeSum_WeightedEnumeration_mem_digits
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_codes_length
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_mem_digits
import Theorems.Thm_WeightedCache_near_card_gibbs
import Theorems.Thm_WeightedCache_ternary_digit_polynomial
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
theorem _root_.solution {N : ℕ} (Q : TritWord N) (D : ℕ) (z : ℝ)
    (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    (WeightedNearEnumeration.codes (wordList Q) D).length*z^D ≤
      ∏ i : Fin N, (if Q i=0 then 1 else if Q i=1 then 1+z^512 else 1+z^513+z^1025) := by
  rw [codes_length_eq_nearWords_card]
  have hh := WeightedCache.near_card_gibbs ![0,512,1025] Q D z hz hz1
  have hp : (∏ i : Fin N, ∑ r : Fin 3, WeightedCache.digitWeight ![0,512,1025] z (Q i) r) =
      ∏ i : Fin N, (if Q i=0 then 1 else if Q i=1 then 1+z^512 else 1+z^513+z^1025) := by
    apply Finset.prod_congr rfl
    intro i _
    simpa using WeightedCache.ternary_digit_polynomial 512 1025 z (Q i)
  simpa only [←hp,nearWords] using hh
end ThreeSum.WeightedNearBankEnumeration
