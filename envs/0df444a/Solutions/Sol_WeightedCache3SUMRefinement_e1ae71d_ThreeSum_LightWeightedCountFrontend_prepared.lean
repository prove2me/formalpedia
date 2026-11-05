-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.prepared
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:12:59.109092+00:00
-- url     : https://prove2.me/submissions/6f8b7990-1f7d-41d0-931c-da4ead4b4a89

import Definitions.Def_Submission_ThreeSum_ReportingHostRelocation
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GroupBankResources
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_WantedRows
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_CountFrontend

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.WeightedBankEnumeration (cacheCost)
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.WeightedBankStageModel
open ThreeSum.LightWeightedNearPair ThreeSum.LightWeightedWantedRowDispatch ThreeSum.LightWeightedPreparedState
set_option maxHeartbeats 8000000
set_option maxRecDepth 18000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend
theorem _root_.solution : program[60]?=some (LightWeightedPreparedWanted.body preparedEntries) := rfl
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend
