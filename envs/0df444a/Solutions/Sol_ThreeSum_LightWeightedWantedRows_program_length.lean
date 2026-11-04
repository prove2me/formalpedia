-- Prove2me | solution 1 for ThreeSum.LightWeightedWantedRows.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:06:36.707074+00:00
-- url     : https://prove2.me/submissions/b27fc205-879e-47fe-8d26-83be118ac819

import Definitions.Def_Submission_Weighted_WantedRowDispatch
import Definitions.Def_Submission_Weighted_PreparedState
import Definitions.Def_Submission_Weighted_WantedRows

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedWantedRows
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.WeightedBankEnumeration (cacheCost)
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.WeightedBankStageModel
open ThreeSum.LightWeightedNearPair ThreeSum.LightWeightedWantedRowDispatch ThreeSum.LightWeightedPreparedState
set_option maxHeartbeats 7000000
set_option maxRecDepth 18000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightWeightedWantedRows
theorem _root_.solution : program.length=43 := rfl
end ThreeSum.LightWeightedWantedRows
