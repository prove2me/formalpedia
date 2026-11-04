-- Prove2me | solution 1 for ThreeSum.WeightedGlobalConcreteProfile.Profile.tag_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T00:49:22.072217+00:00
-- url     : https://prove2.me/submissions/d9c7de91-8c3a-466c-8d6b-d0e334fefadb

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFixedParameters
import Definitions.Def_Submission_Weighted_Global_TernaryExecutableParameters
import Definitions.Def_Submission_Weighted_Global_TernaryColoredSolverNeed
import Definitions.Def_Submission_Weighted_Global_TernaryFastProgramResources
import Definitions.Def_Submission_Weighted_Global_TernaryActualRuntimeParameters
import Definitions.Def_Submission_Weighted_Global_TernaryConcreteProfile
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFixedParameters_radix_tag_bound


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
theorem _root_.solution (P : Profile κ) : P.radix≤2*(4^fixedLength P.m)+1 :=
  radix_tag_bound P.K_pos P.radix_gt_one.le P.minor
end ThreeSum.WeightedGlobalConcreteProfile.Profile
