-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalE4PowerHolomorphic_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:21:33.179702+00:00
-- url     : https://prove2.me/submissions/964a4ec0-af76-4c96-ab48-acb0237051f7

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ReciprocalPolynomialCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicIntegral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicFractionRoot
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationChartEvaluation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalE4Equation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalE4CubePower_apply


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
local notation "R" => LPSOriginalHolomorphicRing
local notation "H" => LPSOriginalHolomorphicFractionField
local notation "P" => Polynomial ℂ
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (k : ℕ) (τ : ℍ) :
    (lpsOriginalE4PowerHolomorphic k).val τ = (ModularForm.E₄ τ^3)^k :=
  lpsOriginalE4CubePower_apply k τ
end QEC.Coding.TannerLiftedProduct
