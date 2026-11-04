-- Prove2me | solution 1 for ThreeSum.WeightedGlobalConcreteProfile.Profile.cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T00:29:01.799367+00:00
-- url     : https://prove2.me/submissions/1ff2ceaf-ce1f-4da7-957c-7a1da0f0ff45

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFixedParameters
import Definitions.Def_Submission_Weighted_Global_TernaryExecutableParameters
import Definitions.Def_Submission_Weighted_Global_TernaryColoredSolverNeed
import Definitions.Def_Submission_Weighted_Global_TernaryFastProgramResources
import Definitions.Def_Submission_Weighted_Global_TernaryActualRuntimeParameters
import Definitions.Def_Submission_Weighted_Global_TernaryConcreteProfile

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
theorem _root_.solution (P : Profile κ) (a b : ZMod P.p) :
    ∃i, WeightedGlobalCoverFrequency.Covers P.m P.p P.cap P.threshold (P.maps i) (a,b) :=
  WeightedGlobalExecutableParameters.cover P.K_pos P.blockPositive P.k_pos a b
end ThreeSum.WeightedGlobalConcreteProfile.Profile
