-- Prove2me | solution 1 for ThreeSum.TernaryFrozenQueryCost.visits_cons_all
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:12:49.705825+00:00
-- url     : https://prove2.me/submissions/0f61d4b0-8a5e-4d2b-a153-95ba1d72e5a3

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
theorem _root_.solution (q : Fin 3) (qs : List ℕ) (D : ℕ) (hD : 2≤D) :
    TernaryNearEnumeration.visits (q.val::qs) D=
      1+∑ d : Fin 3, if d≤q then
        TernaryNearEnumeration.visits qs (D-(q.val-d.val)) else 0 := by
  have hD1 : 1≤D := by omega
  fin_cases q <;> simp [TernaryNearEnumeration.visits,TernaryNearEnumeration.digits,
    List.range_succ,Fin.sum_univ_succ,Fin.le_def,hD,hD1,Nat.add_assoc]
end ThreeSum.TernaryFrozenQueryCost
