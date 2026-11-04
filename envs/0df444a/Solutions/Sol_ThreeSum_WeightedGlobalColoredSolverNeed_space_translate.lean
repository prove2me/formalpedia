-- Prove2me | solution 1 for ThreeSum.WeightedGlobalColoredSolverNeed.space_translate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T22:21:55.178204+00:00
-- url     : https://prove2.me/submissions/18b9b4bf-1453-46fb-b8e6-626abe6530a0

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaAllocationResources
import Definitions.Def_Submission_Weighted_Global_LightTernaryColorPreparationProof
import Definitions.Def_Submission_ThreeSum_TernaryColorPreludeResources_w3sum_ac885d1
import Definitions.Def_Submission_Weighted_Global_TernaryColoredSolverNeed

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredSolverNeed
open Light WeightedGlobalArenaLayout WeightedGlobalArenaAllocation WeightedGlobalArenaPrefixFootprints
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters LightWeightedGlobalColorPreparation
set_option maxHeartbeats 500000
set_option maxRecDepth 24000
variable {p m F : ℕ} [Fact p.Prime]
namespace ThreeSum.WeightedGlobalColoredSolverNeed
theorem _root_.solution (free n J U : ℕ) :
    LightWeightedGlobalColorPreparationProof.space free n J U=
      free+LightWeightedGlobalColorPreparationProof.space 0 n J U := by
  unfold LightWeightedGlobalColorPreparationProof.space arenaFree work oMatrix positions carry cMatrix bMatrix headerAt
  omega
end ThreeSum.WeightedGlobalColoredSolverNeed
