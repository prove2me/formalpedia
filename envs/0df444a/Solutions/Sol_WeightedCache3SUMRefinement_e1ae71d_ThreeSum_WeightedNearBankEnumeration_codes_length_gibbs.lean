-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearBankEnumeration.codes_length_gibbs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:22:11.453973+00:00
-- url     : https://prove2.me/submissions/a6fca794-c691-4365-99ce-ca3fc01941b2

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankEnumeration
import Mathlib.Data.List.Forall2
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearBankEnumeration
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearBankEnumeration_mem_nearWords
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearBankEnumeration_codes_length_eq_nearWords_card
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedAddresses_codes_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankEnumeration_mem_bank
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankEnumeration_wordList_cost
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankEnumeration_wordList_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_digitCost_one
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_digitCost_two
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_digitCost_zero
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_mem_digits
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearEnumeration_codes_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearEnumeration_mem_digits
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_WeightedCache_near_card_gibbs
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_WeightedCache_ternary_digit_polynomial
attribute [local simp] ThreeSum.TernaryAddresses.codes_length
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedAddresses.codes_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankEnumeration.mem_bank
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankEnumeration.wordList_cost
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankEnumeration.wordList_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.digitCost_one
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.digitCost_two
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.digitCost_zero
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.mem_digits
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearEnumeration.codes_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearEnumeration.mem_digits


attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearBankEnumeration.mem_nearWords

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearBankEnumeration
open ThreeSum.TernaryJointType ThreeSum.WeightedBankEnumeration
open WeightedCache (Below)
open ThreeSum.WeightedEnumeration (digitCost)
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearBankEnumeration
theorem _root_.solution {N : ℕ} (Q : TritWord N) (D : ℕ) (z : ℝ)
    (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    (WeightedNearEnumeration.codes (wordList Q) D).length*z^D ≤
      ∏ i : Fin N, (if Q i=0 then 1 else if Q i=1 then 1+z^1369 else 1+z^1371+z^2740) := by
  rw [codes_length_eq_nearWords_card]
  have hh := WeightedCache.near_card_gibbs ![0,1369,2740] Q D z hz hz1
  have hp : (∏ i : Fin N, ∑ r : Fin 3, WeightedCache.digitWeight ![0,1369,2740] z (Q i) r) =
      ∏ i : Fin N, (if Q i=0 then 1 else if Q i=1 then 1+z^1369 else 1+z^1371+z^2740) := by
    apply Finset.prod_congr rfl
    intro i _
    simpa using WeightedCache.ternary_digit_polynomial 1369 2740 z (Q i)
  simpa only [←hp,nearWords] using hh
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearBankEnumeration
