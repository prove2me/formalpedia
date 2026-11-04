-- Prove2me | solution 1 for ThreeSum.WeightedGlobalConcreteProfile.Profile.local_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T00:24:36.79056+00:00
-- url     : https://prove2.me/submissions/c8bc9a08-177c-42a7-bffe-15079e711b40

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFixedParameters
import Definitions.Def_Submission_Weighted_Global_TernaryExecutableParameters
import Definitions.Def_Submission_Weighted_Global_TernaryColoredSolverNeed
import Definitions.Def_Submission_Weighted_Global_TernaryFastProgramResources
import Definitions.Def_Submission_Weighted_Global_TernaryActualRuntimeParameters
import Definitions.Def_Submission_Weighted_Global_TernaryConcreteProfile
import Theorems.Thm_ThreeSum_WeightedGlobalExecutableParameters_source_nonempty


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
theorem _root_.solution (P : Profile κ) (right : Bool) :
    0<(WeightedGlobalNativeCompleteFrontend.localRecords P.maps P.cap right).length :=
  WeightedGlobalExecutableParameters.source_nonempty P.K_pos P.blockPositive P.k_pos right
end ThreeSum.WeightedGlobalConcreteProfile.Profile
