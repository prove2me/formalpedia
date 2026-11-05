-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGroupedBanks.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:19:29.658898+00:00
-- url     : https://prove2.me/submissions/ea2d492a-e0a5-4289-8044-c44b882639c3

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GroupBankStep
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GroupedBanks

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGroupedBanks
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.WeightedBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.LightWeightedBankSweep
set_option maxHeartbeats 6000000
variable {lim : Limits}
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGroupedBanks
theorem _root_.solution : program.length=20 := rfl
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGroupedBanks
