-- Prove2me | solution 1 for ThreeSum.TernaryFrozenQueryCost.work_le_visits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:14:55.638753+00:00
-- url     : https://prove2.me/submissions/2906ee9b-9496-428f-b466-48c6b01c21c2

import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryNearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryCost
import Theorems.Thm_ThreeSum_TernaryFrozenQueryCost_visits_pos
import Theorems.Thm_ThreeSum_TernaryFrozenQueryCost_rank_update_loss
import Theorems.Thm_ThreeSum_TernaryFrozenQueryCost_caps_update_of_not_mem
import Theorems.Thm_ThreeSum_TernaryFrozenQueryCost_visits_cons_all
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_sum
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_codes_length
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_digits
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
open ThreeSum ThreeSum.TernaryFrozenQueryCost
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryQuery
set_option maxHeartbeats 2000000
namespace ThreeSum.TernaryFrozenQueryCost
theorem _root_.solution {N : ℕ} (T : ℕ) (coords : List (Fin N))
    (hcoords : coords.Nodup) (R : TritWord N) :
    work T coords R≤TernaryNearEnumeration.visits (caps coords R) (rank R+1-T) := by
  induction coords generalizing R with
  | nil => simp [work,caps,TernaryNearEnumeration.visits]
  | cons i rest ih =>
    obtain ⟨hi,hn⟩ := List.nodup_cons.mp hcoords
    by_cases hbank : rank R≤T
    · simpa [work,hbank] using visits_pos (caps (i::rest) R) (rank R+1-T)
    · have hD : 2≤rank R+1-T := by omega
      simp only [work,hbank,↓reduceIte,caps,List.map_cons]
      rw [visits_cons_all (R i) _ _ hD]
      apply Nat.add_le_add_left
      apply Finset.sum_le_sum
      intro d hd
      by_cases hlow : d≤R i
      · simp only [hlow,↓reduceIte]
        have hr := rank_update_loss R i d hlow
        have hbudget : rank (Function.update R i d)+1-T=
            (rank R+1-T)-((R i).val-d.val) := by omega
        have hc := ih hn (Function.update R i d)
        rw [hbudget,caps_update_of_not_mem rest R i d hi] at hc
        exact hc
      · simp [hlow]
end ThreeSum.TernaryFrozenQueryCost
