-- Prove2me | solution 1 for ThreeSum.LightWeightedGroupBankStep.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:07:23.354219+00:00
-- url     : https://prove2.me/submissions/16d3bf5f-cdb1-4c3b-9530-6f3401b0a1a8

import Definitions.Def_Submission_Weighted_BankResources
import Definitions.Def_Submission_Weighted_GroupBankStep

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGroupBankStep
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.WeightedBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.LightWeightedBankSweep
set_option maxHeartbeats 5000000
variable {lim : Limits}
namespace ThreeSum.LightWeightedGroupBankStep
theorem _root_.solution : program.length=19 := by rfl
end ThreeSum.LightWeightedGroupBankStep
