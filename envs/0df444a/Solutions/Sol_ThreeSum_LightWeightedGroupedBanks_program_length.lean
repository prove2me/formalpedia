-- Prove2me | solution 1 for ThreeSum.LightWeightedGroupedBanks.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:16:24.758557+00:00
-- url     : https://prove2.me/submissions/77c0d9ba-78b1-4db3-8cff-efb088c19b6f

import Definitions.Def_Submission_Weighted_GroupBankStep
import Definitions.Def_Submission_Weighted_GroupedBanks

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGroupedBanks
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.WeightedBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.LightWeightedBankSweep
set_option maxHeartbeats 6000000
variable {lim : Limits}
namespace ThreeSum.LightWeightedGroupedBanks
theorem _root_.solution : program.length=20 := rfl
end ThreeSum.LightWeightedGroupedBanks
