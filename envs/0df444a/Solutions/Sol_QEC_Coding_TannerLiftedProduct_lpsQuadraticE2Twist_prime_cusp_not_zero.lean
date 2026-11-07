-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Twist_prime_cusp_not_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:09:52.551196+00:00
-- url     : https://prove2.me/submissions/8252df58-67c9-4ec1-ad92-e7d1ec9f648a

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Twist_prime_cusp_tendsto
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2PrimeCuspConstant_ne_zero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] (hq2 : q≠2) :
    ¬UpperHalfPlane.IsZeroAtImInfty
      (lpsQuadraticE2Twist q ∣[(2:ℤ)] lpsE2PrimeCuspMatrix q) := by
  intro hzero
  have h := tendsto_nhds_unique (lpsQuadraticE2Twist_prime_cusp_tendsto q hq2) hzero
  exact lpsQuadraticE2PrimeCuspConstant_ne_zero q hq2 h
end QEC.Coding.TannerLiftedProduct
