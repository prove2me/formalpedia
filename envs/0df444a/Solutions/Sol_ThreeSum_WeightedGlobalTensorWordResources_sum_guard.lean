-- Prove2me | solution 1 for ThreeSum.WeightedGlobalTensorWordResources.sum_guard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T16:16:09.109202+00:00
-- url     : https://prove2.me/submissions/8805353d-8463-4059-b901-7638c30dca3e

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryTensorFactoryReady
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_Weighted_Global_TernaryTensorWordResources
import Theorems.Thm_ThreeSum_WeightedGlobalTensorWordResources_polynomial_bound
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_bound


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalTensorWordResources
open LightTernaryPairedPolynomial TernaryPairedColumnEnumeration StageBounds
namespace ThreeSum.WeightedGlobalTensorWordResources
theorem _root_.solution (K J count V sourceU : ℕ) :
    (count : ℤ)*((J+2)^width K : ℕ)*(polynomial K).bound V≤(word K J count V sourceU : ℤ) := by
  have hp := mul_le_mul_of_nonneg_left (polynomial_bound K V)
    (show (0 : ℤ)≤(count : ℤ)*((J+2)^width K : ℕ) by positivity)
  apply hp.trans
  exact_mod_cast (show count*(J+2)^width K*polynomialBound K V≤word K J count V sourceU by
    unfold word; omega)
end ThreeSum.WeightedGlobalTensorWordResources
