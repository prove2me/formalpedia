-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredSolverNeed.preparation_space
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:28:23.610211+00:00
-- url     : https://prove2.me/submissions/a927b643-a243-4e98-9865-102715f422b5

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaAllocationResources
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryColorPreparationProof
import Definitions.Def_Submission_ThreeSum_TernaryColorPreludeResources_w3sum_ac885d1
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredSolverNeed
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalColoredSolverNeed_preparation_space_general

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredSolverNeed
open Light WeightedGlobalArenaLayout WeightedGlobalArenaAllocation WeightedGlobalArenaPrefixFootprints
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters LightWeightedGlobalColorPreparation
set_option maxHeartbeats 500000
set_option maxRecDepth 24000
variable {p m F : ℕ} [Fact p.Prime]
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredSolverNeed
theorem _root_.solution (M b n U : ℕ) :
    LightWeightedGlobalColorPreparationProof.space 0 n (LightWeightedGlobalDimensions.J M b n U) U≤
      preparationCells M b n U := preparation_space_general n U _
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredSolverNeed
