-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalClearedPolePolynomialSeries_localization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:40:07.251631+00:00
-- url     : https://prove2.me/submissions/9e208fac-9a09-4d33-8de5-f02e88bfcb1d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerQExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCyclotomicCoefficients
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.Localization.Away.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspSeriesReduction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspParameter_cancelPowers
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
theorem _root_.solution {R : Type*} [CommRing R]
    (F : PowerSeries R) (m : ℕ) (P : Polynomial R) :
    algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R)
      (lpsOriginalClearedPolePolynomialSeries F m P.natDegree P)=
      (algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R) PowerSeries.X)^(m*P.natDegree) *
        P.eval₂ ((algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R)).comp PowerSeries.C)
          ((IsLocalization.Away.invSelf (S:=lpsOriginalCuspSeriesRing R)
              (PowerSeries.X : PowerSeries R))^m *
            algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R) F) := by
  classical
  rw [lpsOriginalClearedPolePolynomialSeries,map_sum,Polynomial.eval₂_eq_sum_range,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hiD : i≤P.natDegree := by
    have hi':i<P.natDegree+1 := Finset.mem_range.mp hi
    omega
  simp only [map_mul,map_pow,RingHom.comp_apply]
  symm
  calc
    _ = (algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R) (PowerSeries.C (P.coeff i))) *
        ((algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R) PowerSeries.X)^(m*P.natDegree) *
          (IsLocalization.Away.invSelf (S:=lpsOriginalCuspSeriesRing R)
            (PowerSeries.X : PowerSeries R))^(m*i)) *
        (algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R) F)^i := by
      rw [mul_pow,←pow_mul]
      ring
    _ = _ := by rw [lpsOriginalCuspParameter_cancelPowers m P.natDegree i hiD]
end QEC.Coding.TannerLiftedProduct
