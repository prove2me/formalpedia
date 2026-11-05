-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPreparedWanted.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:59:09.455277+00:00
-- url     : https://prove2.me/submissions/d1a0392a-6065-445d-bb88-f70e44e3f8d8

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_QueryPlan
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearCanonical
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_PreparedWanted

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPreparedWanted
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.WeightedBankEnumeration (cacheCost)
open ThreeSum.TernaryEuler ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages
open ThreeSum.WeightedBankStageModel ThreeSum.LightWeightedNearPair ThreeSum.LightWeightedQueryPlan
set_option maxHeartbeats 6000000
set_option maxRecDepth 16000
variable {lim : Limits} {P : Program}
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPreparedWanted
theorem _root_.solution : program.length=41 := rfl
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPreparedWanted
