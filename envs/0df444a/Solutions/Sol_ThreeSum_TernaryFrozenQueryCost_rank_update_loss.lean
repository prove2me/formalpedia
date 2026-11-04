-- Prove2me | solution 1 for ThreeSum.TernaryFrozenQueryCost.rank_update_loss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:12:47.445057+00:00
-- url     : https://prove2.me/submissions/2f9f0da3-f6be-4105-8060-3ea907b25437

import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryNearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryCost
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_sum
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryBank_rank_add_deficit
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_codes_length
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryQuery_update_below
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
theorem _root_.solution {N : ℕ} (R : TritWord N) (i : Fin N) (d : Fin 3)
    (hd : d≤R i) : rank (Function.update R i d)+((R i).val-d.val)=rank R := by
  have hh := rank_add_deficit (update_below R i d hd)
  have hdef : deficit R (Function.update R i d)=(R i).val-d.val := by
    unfold deficit
    have hterm (j : Fin N) : (R j).val-(Function.update R i d j).val =
        if j=i then (R i).val-d.val else 0 := by
      by_cases hj : j=i
      · subst j; simp
      · simp [Function.update_of_ne hj,hj]
    simp_rw [hterm]
    simp
  simpa [hdef] using hh
end ThreeSum.TernaryFrozenQueryCost
