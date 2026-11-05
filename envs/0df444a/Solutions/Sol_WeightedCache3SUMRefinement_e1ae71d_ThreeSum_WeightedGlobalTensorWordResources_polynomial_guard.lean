-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalTensorWordResources.polynomial_guard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T12:50:50.188188+00:00
-- url     : https://prove2.me/submissions/ab67a86d-d877-4268-ac01-e74145454d38

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryTensorFactoryReady
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryTensorWordResources
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalTensorWordResources_polynomial_expression

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalTensorWordResources
open LightTernaryPairedPolynomial TernaryPairedColumnEnumeration StageBounds
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalTensorWordResources
theorem _root_.solution (K J count V sourceU : ℕ) :
    (polynomial K).coefficient*((V : ℤ)+1)^(polynomial K).degree≤(word K J count V sourceU : ℤ) := by
  rw [polynomial_expression]
  exact_mod_cast (show polynomialBound K V≤word K J count V sourceU by unfold word; omega)
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalTensorWordResources
