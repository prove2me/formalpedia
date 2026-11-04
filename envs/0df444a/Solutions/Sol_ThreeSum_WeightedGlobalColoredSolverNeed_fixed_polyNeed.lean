-- Prove2me | solution 1 for ThreeSum.WeightedGlobalColoredSolverNeed.fixed_polyNeed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T22:41:00.586361+00:00
-- url     : https://prove2.me/submissions/33b5dac1-7054-436e-a1f3-b46f1fc8be34

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaAllocationResources
import Definitions.Def_Submission_Weighted_Global_LightTernaryColorPreparationProof
import Definitions.Def_Submission_ThreeSum_TernaryColorPreludeResources_w3sum_ac885d1
import Definitions.Def_Submission_Weighted_Global_TernaryColoredSolverNeed
import Theorems.Thm_ThreeSum_WeightedGlobalColoredSolverNeed_polyNeed
import Theorems.Thm_ThreeSum_WeightedGlobalColoredSolverNeed_polyNeed_power
import Theorems.Thm_ThreeSum_TernaryColorPreludeResources_polyNeed
import Theorems.Thm_ThreeSum_WeightedFrontendResources_polyNeed
import Theorems.Thm_ThreeSum_WeightedGlobalArenaAllocationResources_polyNeed
import Theorems.Thm_ThreeSum_WeightedGlobalFrontendResources_polyNeed
import Theorems.Thm_ThreeSum_WeightedGlobalMomentChannelResources_polyNeed
import Theorems.Thm_ThreeSum_WeightedGlobalMomentDetectorResources_polyNeed


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredSolverNeed
open Light WeightedGlobalArenaLayout WeightedGlobalArenaAllocation WeightedGlobalArenaPrefixFootprints
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters LightWeightedGlobalColorPreparation
set_option maxHeartbeats 500000
set_option maxRecDepth 24000
variable {p m F : ℕ} [Fact p.Prime]
namespace ThreeSum.WeightedGlobalColoredSolverNeed
theorem _root_.solution {maps : Fin F→Weight m p} {τ cap M b K H drift scale : ℕ}
    (Alloc : Allocation maps τ cap M b K H drift scale) (hM : 1<M) (hb : 1<b) (κ : ℕ) :
    PolyNeed (fixedNeed Alloc κ) := polyNeed_power (polyNeed Alloc hM hb) κ
end ThreeSum.WeightedGlobalColoredSolverNeed
