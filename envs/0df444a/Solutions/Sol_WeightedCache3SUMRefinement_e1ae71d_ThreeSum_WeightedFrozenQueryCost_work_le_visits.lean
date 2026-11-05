-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedFrozenQueryCost.work_le_visits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:19:06.891273+00:00
-- url     : https://prove2.me/submissions/0b6b5ac2-4f3e-4eca-89eb-4d0f69e19278

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Cache
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryCost
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_FrozenQueryCost
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedFrozenQueryCost_cost_update_loss
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedFrozenQueryCost_caps_update
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedFrozenQueryCost_visits_pos
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedFrozenQueryCost_visits_cons_all
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_sum
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryFrozenQueryCost_visits_cons_all
import Theorems.Thm_ThreeSum_TernaryFrozenQueryCost_visits_pos
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
    (hcoords : coords.Nodup) (R : Word N) :
    work T coords R ≤ WeightedNearEnumeration.visits (caps coords R)
      (cacheCost R+2739-T) := by
  induction coords generalizing R with
  | nil => simp [work,caps,WeightedNearEnumeration.visits]
  | cons i rest ih =>
    obtain ⟨hi,hn⟩ := List.nodup_cons.mp hcoords
    by_cases hb : cacheCost R≤T
    · simpa [work,hb] using visits_pos (caps (i::rest) R) (cacheCost R+2739-T)
    · have hD : 2740≤cacheCost R+2739-T := by omega
      simp only [work,hb,↓reduceIte,caps,List.map_cons]
      rw [visits_cons_all (R i) _ _ hD]
      apply Nat.add_le_add_left
      apply sum_le_sum
      intro d _
      by_cases hd : d≤R i
      · simp only [hd,↓reduceIte]
        have hr := cost_update_loss R i d hd
        have hbudget : cacheCost (Function.update R i d)+2739-T =
            (cacheCost R+2739-T)-(digitCost (R i).val-digitCost d.val) := by omega
        have hh := ih hn (Function.update R i d)
        rw [hbudget,caps_update rest R i d hi] at hh
        exact hh
      · simp [hd]
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedFrozenQueryCost
