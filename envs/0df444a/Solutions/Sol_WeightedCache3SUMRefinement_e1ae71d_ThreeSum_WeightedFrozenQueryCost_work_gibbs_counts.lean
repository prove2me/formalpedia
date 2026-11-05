-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedFrozenQueryCost.work_gibbs_counts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:23:16.742209+00:00
-- url     : https://prove2.me/submissions/3d9074d5-4bed-47ca-b2af-e3603aef318f

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Cache
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryCost
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_FrozenQueryCost
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedFrozenQueryCost_work_le_capWord_card
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedFrozenQueryCost_polynomial_product_counts
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_sum
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryFrozenQueryCost_work_le_capWord_card
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_codes_length
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_digits
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedAddresses_codes_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankEnumeration_mem_bank
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankEnumeration_wordList_cost
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankEnumeration_wordList_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_digitCost_one
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_digitCost_two
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_digitCost_zero
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_mem_digits
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearBankEnumeration_mem_nearWords
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearEnumeration_codes_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearEnumeration_mem_digits
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_WeightedCache_near_card_gibbs
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_WeightedCache_ternary_digit_polynomial
attribute [local simp] ThreeSum.TernaryAddresses.codes_length
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
attribute [local simp] ThreeSum.TernaryBankEnumeration.wordList_length
attribute [local simp] ThreeSum.TernaryBankEnumeration.wordList_sum
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits
attribute [local simp] ThreeSum.TernaryNearEnumeration.codes_length
attribute [local simp] ThreeSum.TernaryNearEnumeration.mem_digits
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedAddresses.codes_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankEnumeration.mem_bank
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankEnumeration.wordList_cost
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankEnumeration.wordList_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.digitCost_one
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.digitCost_two
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.digitCost_zero
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.mem_digits
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearBankEnumeration.mem_nearWords
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearEnumeration.codes_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearEnumeration.mem_digits



set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedFrozenQueryCost
open Finset WeightedCache WeightedEnumeration
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedFrozenQueryCost
theorem _root_.solution {N : ℕ} (T : ℕ) (coords : List (Fin N))
    (hcoords : coords.Nodup) (R : Word N) (z : ℝ) (hz : 0≤z) (hz1 : z≤1) :
    (work T coords R : ℝ)*z^(cacheCost R+2739-T) ≤
      (coords.length+1)*(1+z^1369)^TernaryJointType.digitCount (capWord coords R) 1 *
        (1+z^1371+z^2740)^TernaryJointType.digitCount (capWord coords R) 2 := by
  have hwork : (work T coords R : ℝ)≤
      (coords.length+1)*(WeightedNearBankEnumeration.nearWords (capWord coords R) (cacheCost R+2739-T)).card := by
    exact_mod_cast work_le_capWord_card T coords hcoords R
  have hg := WeightedCache.near_card_gibbs ![0,1369,2740] (capWord coords R)
    (cacheCost R+2739-T) z hz hz1
  have hp : (∏ i : Fin coords.length, ∑ r : Fin 3,
      WeightedCache.digitWeight ![0,1369,2740] z (capWord coords R i) r) =
      (1+z^1369)^TernaryJointType.digitCount (capWord coords R) 1 *
        (1+z^1371+z^2740)^TernaryJointType.digitCount (capWord coords R) 2 := by
    rw [←polynomial_product_counts]
    apply prod_congr rfl
    intro i _
    exact WeightedCache.ternary_digit_polynomial 1369 2740 z _
  rw [hp] at hg
  calc
    _ ≤ ((coords.length+1)*(WeightedNearBankEnumeration.nearWords (capWord coords R)
        (cacheCost R+2739-T)).card)*z^(cacheCost R+2739-T) :=
      mul_le_mul_of_nonneg_right hwork (pow_nonneg hz _)
    _ = (coords.length+1)*((WeightedNearBankEnumeration.nearWords (capWord coords R)
        (cacheCost R+2739-T)).card*z^(cacheCost R+2739-T)) := by ring
    _ ≤ _ := by
      simpa only [WeightedNearBankEnumeration.nearWords,mul_assoc] using
        mul_le_mul_of_nonneg_left hg (by positivity : (0 : ℝ)≤coords.length+1)
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedFrozenQueryCost
