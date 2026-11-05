-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedWantedRows.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:10:00.722585+00:00
-- url     : https://prove2.me/submissions/af5a9ea7-c4b6-4482-a845-04376c95eee7

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_WantedRowDispatch
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_PreparedState
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_WantedRows

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedWantedRows
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.WeightedBankEnumeration (cacheCost)
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.WeightedBankStageModel
open ThreeSum.LightWeightedNearPair ThreeSum.LightWeightedWantedRowDispatch ThreeSum.LightWeightedPreparedState
set_option maxHeartbeats 7000000
set_option maxRecDepth 18000
variable {lim : Limits} {P : Program}
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedWantedRows
theorem _root_.solution : program.length=43 := rfl
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedWantedRows
