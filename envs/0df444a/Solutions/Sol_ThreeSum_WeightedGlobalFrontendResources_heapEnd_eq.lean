-- Prove2me | solution 1 for ThreeSum.WeightedGlobalFrontendResources.heapEnd_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:26:49.165088+00:00
-- url     : https://prove2.me/submissions/d4d55043-17a1-4018-9978-37e192f7f21e

import Definitions.Def_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_Weighted_Global_TernaryRadixOverhead
import Definitions.Def_Submission_Weighted_Global_FrontendResources

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
theorem _root_.solution (a N R A : ℕ) :
    heapEnd a N R A=a+(4*N+6)*R+6*N+2*eulerBound N A+7 := by
  unfold heapEnd out gws division vals ranks fws powers active caps
  ring
end ThreeSum.WeightedGlobalFrontendResources
