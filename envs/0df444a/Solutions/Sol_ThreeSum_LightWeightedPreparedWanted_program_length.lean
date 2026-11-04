-- Prove2me | solution 1 for ThreeSum.LightWeightedPreparedWanted.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:42:44.990323+00:00
-- url     : https://prove2.me/submissions/b1a7cb68-a231-495e-bec7-e3901a0fbe24

import Definitions.Def_Submission_Weighted_QueryPlan
import Definitions.Def_Submission_Weighted_NearCanonical
import Definitions.Def_Submission_Weighted_PreparedWanted

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedPreparedWanted
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.WeightedBankEnumeration (cacheCost)
open ThreeSum.TernaryEuler ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages
open ThreeSum.WeightedBankStageModel ThreeSum.LightWeightedNearPair ThreeSum.LightWeightedQueryPlan
set_option maxHeartbeats 6000000
set_option maxRecDepth 16000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightWeightedPreparedWanted
theorem _root_.solution : program.length=41 := rfl
end ThreeSum.LightWeightedPreparedWanted
