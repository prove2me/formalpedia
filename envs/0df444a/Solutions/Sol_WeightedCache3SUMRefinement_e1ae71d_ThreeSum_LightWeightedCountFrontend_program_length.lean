-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:22:32.712052+00:00
-- url     : https://prove2.me/submissions/b5f356e9-44d0-41ba-bf90-c1ade6472e4f

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
theorem _root_.solution : program.length=64 := rfl
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend
