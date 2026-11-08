-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalE4DenominatorEquation_coeff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:36:21.935983+00:00
-- url     : https://prove2.me/submissions/c3e5ac00-3b32-4262-8dfd-c10d055210b8

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ReciprocalPolynomialCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicIntegral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicFractionRoot
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationChartEvaluation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalE4Equation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalE4DenominatorCosetPolynomial_coeff
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalDelta_j_power
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJPolynomialEvalHom_injective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphicRatioEquation_recovery
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_even
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_odd
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (k : ℕ) (A : LPSOriginalMeromorphicLevelForm N k) :
    (lpsOriginalMeromorphicRatioEquation N k A
      (lpsOriginalMeromorphicE4PowerAtLevel N k)).coeff
      (Nat.card (LPSOriginalMeromorphicCosets N)) =
        Polynomial.C ((-1 : ℂ)^Nat.card (LPSOriginalMeromorphicCosets N)) *
          Polynomial.X^(k * Nat.card (LPSOriginalMeromorphicCosets N)) := by
  apply lpsOriginalJPolynomialEvalHom_injective
  funext τ
  change Polynomial.eval (lpsOriginalJInvariant τ) _ =
    Polynomial.eval (lpsOriginalJInvariant τ)
      (Polynomial.C ((-1 : ℂ)^Nat.card (LPSOriginalMeromorphicCosets N)) *
        Polynomial.X^(k * Nat.card (LPSOriginalMeromorphicCosets N)))
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  have h := congrArg (fun p : Polynomial ℂ => p.coeff (Nat.card (LPSOriginalMeromorphicCosets N)))
    (lpsOriginalMeromorphicRatioEquation_recovery N k A
      (lpsOriginalMeromorphicE4PowerAtLevel N k) τ)
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_map,
    lpsOriginalE4DenominatorCosetPolynomial_coeff,
    ← lpsOriginalDelta_j_power (k * Nat.card (LPSOriginalMeromorphicCosets N)) τ] at h
  apply mul_left_cancel₀ (pow_ne_zero (k * Nat.card (LPSOriginalMeromorphicCosets N))
    (ModularForm.discriminant_ne_zero τ))
  simpa only [Polynomial.coe_evalRingHom, mul_assoc, mul_left_comm] using h
end QEC.Coding.TannerLiftedProduct
