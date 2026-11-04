-- Prove2me | solution 1 for ThreeSum.WeightedGlobalNativePairMoments.mass_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:22:25.255751+00:00
-- url     : https://prove2.me/submissions/73d46709-26ee-41fc-98a7-59996501fdff

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryMomentChannelFactory
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalTensorChannels
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalMomentSupport
import Definitions.Def_Submission_ThreeSum_TernaryPairedSupport
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairMoments
import Theorems.Thm_ThreeSum_TernaryConvolution_factorial_pos


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalNativePairMoments
open Finset TernaryJointType
open scoped BigOperators
namespace ThreeSum.WeightedGlobalNativePairMoments
theorem _root_.solution {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (i : ℕ) :
    ∀ p : Pair S i, 0<mass S i p := by
  intro p
  exact TernaryConvolution.factorial_pos _
end ThreeSum.WeightedGlobalNativePairMoments
