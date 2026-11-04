-- Prove2me | solution 1 for ThreeSum.WeightedQueryBudget.prepared_rows_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:04:54.569888+00:00
-- url     : https://prove2.me/submissions/f4cdecef-902b-4d5b-ad93-db047b94c2dc

import Definitions.Def_Submission_Weighted_PreparedWanted
import Definitions.Def_Submission_Weighted_Schedule
import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_Weighted_QueryBudget
import Theorems.Thm_ThreeSum_WeightedQueryBudget_near_card_bound
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryNearBankEnumeration_codes_length_eq_nearWords_card
import Theorems.Thm_ThreeSum_WeightedNearBankEnumeration_codes_length_eq_nearWords_card
import Theorems.Thm_ThreeSum_WeightedNearBankEnumeration_mem_nearWords
import Theorems.Thm_ThreeSum_WeightedSchedule_query_boundary
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
attribute [local simp] ThreeSum.WeightedNearBankEnumeration.mem_nearWords



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedQueryBudget
open Real TernaryJointType WeightedSchedule WeightedCacheParameters
open WeightedBankEnumeration (cacheCost)
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
namespace ThreeSum.WeightedQueryBudget
theorem _root_.solution {m : ℕ} (Q : TritWord (fixedLength m))
    (hQ : HasType Q (fixedPi m)) :
    (LightWeightedPreparedWanted.rows Q (bankCut m) : ℝ)≤envelope m := by
  have hD : LightWeightedPreparedWanted.D Q (bankCut m)≤treeBudget m := by
    have hb := query_boundary hQ
    unfold LightWeightedPreparedWanted.D
    omega
  have hsub : WeightedNearBankEnumeration.nearWords Q (LightWeightedPreparedWanted.D Q (bankCut m))⊆
      WeightedNearBankEnumeration.nearWords Q (treeBudget m) := by
    intro R hR
    rw [WeightedNearBankEnumeration.mem_nearWords] at hR ⊢
    exact ⟨hR.1,hR.2.trans hD⟩
  have hc := Finset.card_le_card hsub
  unfold LightWeightedPreparedWanted.rows
  rw [WeightedNearBankEnumeration.codes_length_eq_nearWords_card]
  have hcR : ((WeightedNearBankEnumeration.nearWords Q (LightWeightedPreparedWanted.D Q (bankCut m))).card : ℝ)≤
      ((WeightedNearBankEnumeration.nearWords Q (treeBudget m)).card : ℝ) := by exact_mod_cast hc
  exact hcR.trans (near_card_bound Q hQ)
end ThreeSum.WeightedQueryBudget
