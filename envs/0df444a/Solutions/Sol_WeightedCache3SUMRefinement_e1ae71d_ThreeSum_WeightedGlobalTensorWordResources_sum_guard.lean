-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalTensorWordResources.sum_guard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T12:52:46.165522+00:00
-- url     : https://prove2.me/submissions/29bc1146-97dd-459e-a0b4-50489358a1b8

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryTensorFactoryReady
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryTensorWordResources
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalTensorWordResources_polynomial_bound
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_bound


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalTensorWordResources
open LightTernaryPairedPolynomial TernaryPairedColumnEnumeration StageBounds
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalTensorWordResources
theorem _root_.solution (K J count V sourceU : ℕ) :
    (count : ℤ)*((J+2)^width K : ℕ)*(polynomial K).bound V≤(word K J count V sourceU : ℤ) := by
  have hp := mul_le_mul_of_nonneg_left (polynomial_bound K V)
    (show (0 : ℤ)≤(count : ℤ)*((J+2)^width K : ℕ) by positivity)
  apply hp.trans
  exact_mod_cast (show count*(J+2)^width K*polynomialBound K V≤word K J count V sourceU by
    unfold word; omega)
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalTensorWordResources
