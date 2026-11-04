-- Prove2me | solution 1 for ThreeSum.LightWeightedCountFrontend.prepared
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:13:07.483788+00:00
-- url     : https://prove2.me/submissions/7961ef7d-8977-433f-8b0c-55f861a5ded2

import Definitions.Def_Submission_ThreeSum_ReportingHostRelocation
import Definitions.Def_Submission_Weighted_GroupBankResources
import Definitions.Def_Submission_Weighted_WantedRows
import Definitions.Def_Submission_Weighted_CountFrontend

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedCountFrontend
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.WeightedBankEnumeration (cacheCost)
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.WeightedBankStageModel
open ThreeSum.LightWeightedNearPair ThreeSum.LightWeightedWantedRowDispatch ThreeSum.LightWeightedPreparedState
set_option maxHeartbeats 8000000
set_option maxRecDepth 18000
namespace ThreeSum.LightWeightedCountFrontend
theorem _root_.solution : program[60]?=some (LightWeightedPreparedWanted.body preparedEntries) := rfl
end ThreeSum.LightWeightedCountFrontend
