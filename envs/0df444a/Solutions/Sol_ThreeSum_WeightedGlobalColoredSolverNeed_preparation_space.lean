-- Prove2me | solution 1 for ThreeSum.WeightedGlobalColoredSolverNeed.preparation_space
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T22:38:13.000725+00:00
-- url     : https://prove2.me/submissions/d6a68522-c8ab-4587-a265-c718486573f0

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaAllocationResources
import Definitions.Def_Submission_Weighted_Global_LightTernaryColorPreparationProof
import Definitions.Def_Submission_ThreeSum_TernaryColorPreludeResources_w3sum_ac885d1
import Definitions.Def_Submission_Weighted_Global_TernaryColoredSolverNeed
import Theorems.Thm_ThreeSum_WeightedGlobalColoredSolverNeed_preparation_space_general

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredSolverNeed
open Light WeightedGlobalArenaLayout WeightedGlobalArenaAllocation WeightedGlobalArenaPrefixFootprints
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters LightWeightedGlobalColorPreparation
set_option maxHeartbeats 500000
set_option maxRecDepth 24000
variable {p m F : ℕ} [Fact p.Prime]
namespace ThreeSum.WeightedGlobalColoredSolverNeed
theorem _root_.solution (M b n U : ℕ) :
    LightWeightedGlobalColorPreparationProof.space 0 n (LightWeightedGlobalDimensions.J M b n U) U≤
      preparationCells M b n U := preparation_space_general n U _
end ThreeSum.WeightedGlobalColoredSolverNeed
