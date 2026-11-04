-- Prove2me | solution 1 for ThreeSum.WeightedGlobalFrontendResources.need_space
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:55:01.886397+00:00
-- url     : https://prove2.me/submissions/9f52bb4e-96c1-4355-b0a6-4e2e2ec3d03c

import Definitions.Def_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_Weighted_Global_TernaryRadixOverhead
import Definitions.Def_Submission_Weighted_Global_FrontendResources
import Theorems.Thm_ThreeSum_WeightedGlobalFrontendResources_heapEnd_translate

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalFrontendResources
open Light ThreeSum.TernaryJointType ThreeSum.WeightedGlobalBank ThreeSum.TernaryEuler
open ThreeSum.LightWeightedNearPair ThreeSum.LightWeightedQueryPlan
open ThreeSum.WeightedBankStageModel ThreeSum.LightWeightedPreparedWanted
open Filter StageBounds ThreeSum.TernaryCodeSemantics
open scoped Topology
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000
namespace ThreeSum.WeightedGlobalFrontendResources
theorem _root_.solution {lim : Limits} {free d N nb groups count R A priorCells hostWord : ℕ}
    (H : (need N nb groups count R A priorCells hostWord).Ok lim free d) :
    heapEnd (free+priorCells) N R A≤ lim.space ∧
    (word N nb groups count R A:ℤ)≤ lim.word ∧ d+5*N+16≤ lim.depth := by
  refine ⟨?_,?_,?_⟩
  · rw [heapEnd_translate]; exact H.cells
  · exact (Int.ofNat_le.mpr (Nat.le_add_left _ _)).trans H.word
  · exact H.depth
end ThreeSum.WeightedGlobalFrontendResources
