-- Prove2me | solution 1 for ThreeSum.WeightedFrontendResources.need_space
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:05:26.444205+00:00
-- url     : https://prove2.me/submissions/4d1c39f6-61dc-40ce-9078-c1d3334cf733

import Definitions.Def_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_ThreeSum_TernaryRadixOverhead
import Definitions.Def_Submission_Weighted_FrontendResources
import Theorems.Thm_ThreeSum_WeightedFrontendResources_heapEnd_translate

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedFrontendResources
open Light ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.LightWeightedNearPair ThreeSum.LightWeightedQueryPlan
open ThreeSum.WeightedBankStageModel ThreeSum.LightWeightedPreparedWanted
open Filter StageBounds ThreeSum.TernaryCodeSemantics
open scoped Topology
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000
namespace ThreeSum.WeightedFrontendResources
theorem _root_.solution {lim : Limits} {free d N nb groups count R A priorCells hostWord : ℕ}
    (H : (need N nb groups count R A priorCells hostWord).Ok lim free d) :
    heapEnd (free+priorCells) N R A≤ lim.space ∧
    (word N nb groups count R A:ℤ)≤ lim.word ∧ d+5*N+16≤ lim.depth := by
  refine ⟨?_,?_,?_⟩
  · rw [heapEnd_translate]; exact H.cells
  · exact (Int.ofNat_le.mpr (Nat.le_add_left _ _)).trans H.word
  · exact H.depth
end ThreeSum.WeightedFrontendResources
