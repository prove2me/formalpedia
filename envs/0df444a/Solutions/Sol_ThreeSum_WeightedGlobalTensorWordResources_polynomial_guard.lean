-- Prove2me | solution 1 for ThreeSum.WeightedGlobalTensorWordResources.polynomial_guard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T16:21:14.48218+00:00
-- url     : https://prove2.me/submissions/5fce035a-9593-4453-9dad-3a02763b5e3e

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryTensorFactoryReady
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_Weighted_Global_TernaryTensorWordResources
import Theorems.Thm_ThreeSum_WeightedGlobalTensorWordResources_polynomial_expression

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalTensorWordResources
open LightTernaryPairedPolynomial TernaryPairedColumnEnumeration StageBounds
namespace ThreeSum.WeightedGlobalTensorWordResources
theorem _root_.solution (K J count V sourceU : ℕ) :
    (polynomial K).coefficient*((V : ℤ)+1)^(polynomial K).degree≤(word K J count V sourceU : ℤ) := by
  rw [polynomial_expression]
  exact_mod_cast (show polynomialBound K V≤word K J count V sourceU by unfold word; omega)
end ThreeSum.WeightedGlobalTensorWordResources
