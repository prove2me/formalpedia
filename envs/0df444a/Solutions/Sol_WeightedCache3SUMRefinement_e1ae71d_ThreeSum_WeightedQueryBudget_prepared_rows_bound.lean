-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedQueryBudget.prepared_rows_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:21:05.401327+00:00
-- url     : https://prove2.me/submissions/a19f19c1-ecfa-455d-80de-fc5d4726f691

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_PreparedWanted
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Schedule
import Definitions.Def_Submission_Weighted_Parameters_w3sum_e1ae71d
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_QueryBudget
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedQueryBudget_near_card_bound
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryNearBankEnumeration_codes_length_eq_nearWords_card
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearBankEnumeration_codes_length_eq_nearWords_card
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearBankEnumeration_mem_nearWords
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedSchedule_query_boundary
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearBankEnumeration.mem_nearWords



set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedQueryBudget
open Real TernaryJointType WeightedSchedule WeightedCacheParameters_e1ae71d
open WeightedBankEnumeration (cacheCost)
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedQueryBudget
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
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedQueryBudget
