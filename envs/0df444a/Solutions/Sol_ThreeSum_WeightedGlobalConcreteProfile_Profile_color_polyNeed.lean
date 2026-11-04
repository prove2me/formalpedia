-- Prove2me | solution 1 for ThreeSum.WeightedGlobalConcreteProfile.Profile.color_polyNeed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T00:36:42.133563+00:00
-- url     : https://prove2.me/submissions/878ed1bc-10de-4b7b-8434-f92355bda42f

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFixedParameters
import Definitions.Def_Submission_Weighted_Global_TernaryExecutableParameters
import Definitions.Def_Submission_Weighted_Global_TernaryColoredSolverNeed
import Definitions.Def_Submission_Weighted_Global_TernaryFastProgramResources
import Definitions.Def_Submission_Weighted_Global_TernaryActualRuntimeParameters
import Definitions.Def_Submission_Weighted_Global_TernaryConcreteProfile
import Theorems.Thm_ThreeSum_WeightedGlobalColoredSolverNeed_fixed_polyNeed


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalConcreteProfile
open Light WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps WeightedGlobalCoverScale
open WeightedGlobalOversizePrime WeightedGlobalOversizeRates WeightedGlobalOversizeOverhead WeightedGlobalSignedPadding
open WeightedGlobalArenaFixedParameters WeightedGlobalArenaBudgetExistence
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
open ThreeSum.WeightedGlobalConcreteProfile.Profile
variable {κ : ℕ}
namespace ThreeSum.WeightedGlobalConcreteProfile.Profile
theorem _root_.solution (P : Profile κ) : PolyNeed P.colorNeed :=
  WeightedGlobalColoredSolverNeed.fixed_polyNeed P.allocation P.M_gt_one P.radix_gt_one κ
end ThreeSum.WeightedGlobalConcreteProfile.Profile
