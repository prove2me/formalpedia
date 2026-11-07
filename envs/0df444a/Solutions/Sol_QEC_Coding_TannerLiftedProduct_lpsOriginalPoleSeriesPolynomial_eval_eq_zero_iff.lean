-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalPoleSeriesPolynomial_eval_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:43:52.019222+00:00
-- url     : https://prove2.me/submissions/58634e95-2c7c-48e8-abb6-1da6691bff66

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerQExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCyclotomicCoefficients
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.Localization.Away.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspSeriesReduction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspSeriesAlgebraMap_injective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedPolePolynomialSeries_constant
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedPolePolynomialSeries_localization
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
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution {R : Type*}
    [CommRing R] [IsDomain R] (F : PowerSeries R)
    (hF : PowerSeries.constantCoeff F=1) (m : ℕ) (hm : 0<m) (P : Polynomial R) :
    P.eval₂ ((algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R)).comp PowerSeries.C)
      ((IsLocalization.Away.invSelf (S:=lpsOriginalCuspSeriesRing R)
        (PowerSeries.X : PowerSeries R))^m *
          algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R) F)=0 ↔ P=0 := by
  constructor
  · intro h
    have hc:=lpsOriginalClearedPolePolynomialSeries_localization F m P
    rw [h,mul_zero] at hc
    have hz : lpsOriginalClearedPolePolynomialSeries F m P.natDegree P=0 :=
      (lpsOriginalCuspSeriesAlgebraMap_injective R)
        (hc.trans ((algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R)).map_zero).symm)
    have hcoeff:=congrArg PowerSeries.constantCoeff hz
    rw [lpsOriginalClearedPolePolynomialSeries_constant F hF m hm P,map_zero] at hcoeff
    exact Polynomial.leadingCoeff_eq_zero.mp hcoeff
  · rintro rfl
    simp
end QEC.Coding.TannerLiftedProduct
