-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativePairMoments.mass_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T12:19:25.041412+00:00
-- url     : https://prove2.me/submissions/9591439b-74d3-4160-8d51-4b3531392745

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryMomentChannelFactory
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalTensorChannels
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalMomentSupport
import Definitions.Def_Submission_ThreeSum_TernaryPairedSupport
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativePairMoments
import Theorems.Thm_ThreeSum_TernaryConvolution_factorial_pos


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativePairMoments
open Finset TernaryJointType
open scoped BigOperators
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativePairMoments
theorem _root_.solution {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (i : ℕ) :
    ∀ p : Pair S i, 0<mass S i p := by
  intro p
  exact TernaryConvolution.factorial_pos _
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativePairMoments
