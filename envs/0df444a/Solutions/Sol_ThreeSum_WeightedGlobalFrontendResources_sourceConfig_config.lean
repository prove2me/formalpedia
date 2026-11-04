-- Prove2me | solution 1 for ThreeSum.WeightedGlobalFrontendResources.sourceConfig_config
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:23:20.327014+00:00
-- url     : https://prove2.me/submissions/f09ba5b2-ffc8-4930-b35f-24eb04803fd8

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
theorem _root_.solution (a N R A bank nb bv T h ws base stride tail group : ℕ) :
    LightWeightedWantedRowDispatch.sourceConfig (config a N R A bank nb bv T h ws)
      base stride tail group=
    config a N R A bank nb (base+group*stride+tail) T h ws := rfl
end ThreeSum.WeightedGlobalFrontendResources
