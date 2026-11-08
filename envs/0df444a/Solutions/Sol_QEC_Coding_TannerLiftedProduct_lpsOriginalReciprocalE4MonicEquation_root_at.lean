-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalReciprocalE4MonicEquation_root_at
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:46:49.587425+00:00
-- url     : https://prove2.me/submissions/c76ea7b5-8bef-4ee9-85c2-c0be644f6eb1

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ReciprocalPolynomialCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicIntegral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicFractionRoot
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationChartEvaluation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalE4Equation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphicE4PowerAtLevel_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalReciprocalE4NormalizedEquation_coeff_degree
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphicRatioEquation_root_at
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_ReciprocalPolynomialCoefficients_reflectCoefficients_root


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (k : ℕ) (A : LPSOriginalMeromorphicLevelForm N k)
    (τ : ℍ) (t : ℂ) (hj : lpsOriginalJInvariant τ ≠ 0)
    (ht : A τ = (ModularForm.E₄ τ^3)^k*t) :
    (lpsOriginalReciprocalE4MonicEquation N k A).eval₂
      (Polynomial.evalRingHom (lpsOriginalJInvariant τ)⁻¹) t = 0 := by
  apply QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients.reflectCoefficients_root
    (k * Nat.card (LPSOriginalMeromorphicCosets N))
    (lpsOriginalReciprocalE4NormalizedEquation N k A)
    (lpsOriginalReciprocalE4NormalizedEquation_coeff_degree N k A)
    (lpsOriginalJInvariant τ) t hj
  rw [lpsOriginalReciprocalE4NormalizedEquation, Polynomial.eval₂_mul]
  have hr := lpsOriginalMeromorphicRatioEquation_root_at N k A
    (lpsOriginalMeromorphicE4PowerAtLevel N k) τ t
    (by rwa [lpsOriginalMeromorphicE4PowerAtLevel_apply])
  rw [hr, mul_zero]
end QEC.Coding.TannerLiftedProduct
