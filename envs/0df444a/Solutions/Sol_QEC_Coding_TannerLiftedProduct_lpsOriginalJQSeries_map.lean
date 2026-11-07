-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJQSeries_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:17:38.615109+00:00
-- url     : https://prove2.me/submissions/f76022af-c217-4df2-8ddc-8f9bf0e63752

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.RingTheory.PowerSeries.Inverse
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalQExpansionArithmetic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_coeff
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_congr
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_mul
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_pow
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalE4QSeries_map
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalDeltaSlopeQSeries_map
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalDeltaSlopeQSeries_constant
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalDeltaSlope_analytic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalDeltaSlope_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJQCoefficient_analytic_zero
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
open Complex Filter Topology UpperHalfPlane ModularForm MatrixGroups
open scoped UpperHalfPlane ModularForm
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    PowerSeries.map (algebraMap ℚ ℂ) lpsOriginalJQSeries=
      lpsOriginalTaylorSeries lpsOriginalJQCoefficient := by
  let D := lpsOriginalTaylorSeries (dslope (cuspFunction 1 ModularForm.discriminant) 0)
  have hD0 : D.coeff 0=1 := by
    simp only [D,lpsOriginalTaylorSeries_coeff,Nat.factorial_zero,
      Nat.cast_one,inv_one,one_mul,iteratedDeriv_zero]
    exact lpsOriginalDeltaSlope_zero
  have hDn : D≠0 := by
    intro h
    have := congrArg (fun S : PowerSeries ℂ => S.coeff 0) h
    rw [hD0,map_zero] at this
    exact one_ne_zero this
  apply mul_left_cancel₀ hDn
  have hL : D*PowerSeries.map (algebraMap ℚ ℂ) lpsOriginalJQSeries=
      (qExpansion 1 ModularForm.E₄)^3 := by
    change lpsOriginalTaylorSeries (dslope (cuspFunction 1 ModularForm.discriminant) 0)*_= _
    rw [←lpsOriginalDeltaSlopeQSeries_map,lpsOriginalJQSeries,←map_mul]
    have hm := PowerSeries.mul_invOfUnit lpsOriginalDeltaSlopeQSeries 1
      lpsOriginalDeltaSlopeQSeries_constant
    rw [mul_left_comm,hm,mul_one,map_pow,lpsOriginalE4QSeries_map]
  have hne : ∀ᶠ q in 𝓝 (0:ℂ), dslope (cuspFunction 1 ModularForm.discriminant) 0 q≠0 := by
    exact lpsOriginalDeltaSlope_analytic.continuousAt.eventually_ne
      (by rw [lpsOriginalDeltaSlope_zero];norm_num)
  have hg : (dslope (cuspFunction 1 ModularForm.discriminant) 0)*lpsOriginalJQCoefficient=ᶠ[𝓝 0]
      (cuspFunction 1 ModularForm.E₄)^3 := by
    filter_upwards [hne] with q hq
    change dslope (cuspFunction 1 ModularForm.discriminant) 0 q*
      ((cuspFunction 1 ModularForm.E₄ q)^3/dslope (cuspFunction 1 ModularForm.discriminant) 0 q)=_
    simp only [Pi.pow_apply]
    field_simp [hq]
  have hR := lpsOriginalTaylorSeries_congr hg
  rw [lpsOriginalTaylorSeries_mul lpsOriginalDeltaSlope_analytic
    lpsOriginalJQCoefficient_analytic_zero,lpsOriginalTaylorSeries_pow
      (ModularFormClass.analyticAt_cuspFunction_zero ModularForm.E₄
        one_pos one_mem_strictPeriods_SL) 3] at hR
  exact hL.trans hR.symm
end QEC.Coding.TannerLiftedProduct
