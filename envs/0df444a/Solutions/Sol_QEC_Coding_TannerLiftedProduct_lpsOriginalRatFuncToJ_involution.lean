-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRatFuncToJ_involution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:45:19.870986+00:00
-- url     : https://prove2.me/submissions/5fa6a559-0b74-4f50-88b6-e17e4a71f20f

import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_TwoChartFiniteDimensionalBridge
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalChartComparison
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRatFuncToJ_X
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseAffinePlace_rationalInvolution_X
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
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
open QEC.Coding.TannerLiftedProduct
open scoped Polynomial RatFunc
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry
noncomputable section
local notation "P" => Polynomial ℂ
local notation "J" => FractionRing P
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (f : RatFunc ℂ) :
    lpsOriginalRatFuncToJ (InverseAffinePlace.rationalInvolution ℂ f) =
      lpsOriginalComplexJFractionInversion (lpsOriginalRatFuncToJ f) := by
  have hp :
      (lpsOriginalRatFuncToJ.toRingHom.comp
        (InverseAffinePlace.rationalInvolution ℂ).toRingHom).comp
          (algebraMap P (RatFunc ℂ)) =
      (lpsOriginalComplexJFractionInversion.comp lpsOriginalRatFuncToJ.toRingHom).comp
        (algebraMap P (RatFunc ℂ)) := by
    apply Polynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, RatFunc.algebraMap_C]
      change lpsOriginalRatFuncToJ
        (InverseAffinePlace.rationalInvolution ℂ (algebraMap ℂ (RatFunc ℂ) c)) =
          lpsOriginalComplexJFractionInversion
            (lpsOriginalRatFuncToJ (algebraMap ℂ (RatFunc ℂ) c))
      simp only [AlgEquiv.commutes, lpsOriginalComplexJFractionInversion_constant]
    · simp only [RingHom.comp_apply, RatFunc.algebraMap_X]
      change lpsOriginalRatFuncToJ (InverseAffinePlace.rationalInvolution ℂ RatFunc.X) =
        lpsOriginalComplexJFractionInversion (lpsOriginalRatFuncToJ RatFunc.X)
      rw [InverseAffinePlace.rationalInvolution_X, map_inv₀,
        lpsOriginalRatFuncToJ_X, lpsOriginalComplexJFractionInversion_X]
  have h : lpsOriginalRatFuncToJ.toRingHom.comp
      (InverseAffinePlace.rationalInvolution ℂ).toRingHom =
      lpsOriginalComplexJFractionInversion.comp lpsOriginalRatFuncToJ.toRingHom := by
    apply IsFractionRing.ringHom_ext (A := P)
    intro p
    exact RingHom.congr_fun hp p
  exact RingHom.congr_fun h f
end QEC.Coding.TannerLiftedProduct
