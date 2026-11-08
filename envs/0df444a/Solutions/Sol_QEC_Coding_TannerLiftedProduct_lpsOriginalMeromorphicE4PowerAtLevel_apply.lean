-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalMeromorphicE4PowerAtLevel_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:21:20.980672+00:00
-- url     : https://prove2.me/submissions/64b47dd8-1659-452b-8f98-10cd8a68406d

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ReciprocalPolynomialCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicIntegral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicFractionRoot
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationChartEvaluation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalE4Equation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalE4CubePower_apply


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N k : ℕ) (τ : ℍ) :
    lpsOriginalMeromorphicE4PowerAtLevel N k τ =
      (ModularForm.E₄ τ^3)^k :=
  lpsOriginalE4CubePower_apply k τ
end QEC.Coding.TannerLiftedProduct
