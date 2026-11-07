-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalDeltaZSeries_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:32:51.371572+00:00
-- url     : https://prove2.me/submissions/e0385e43-e5a5-4634-a8d5-44266dc75c0f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalQExpansionArithmetic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerQExpansion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalE4QSeries_sigma
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalE6QSeries_sigma
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalSigmaCombinationZSeries_map
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
open Complex Filter Topology
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    PowerSeries.map (algebraMap ℤ ℚ) lpsOriginalDeltaZSeries=lpsOriginalDeltaQSeries := by
  let A := PowerSeries.map (algebraMap ℤ ℚ) (lpsOriginalSigmaZSeries 3)
  let B := PowerSeries.map (algebraMap ℤ ℚ) (lpsOriginalSigmaZSeries 5)
  let T := PowerSeries.map (algebraMap ℤ ℚ) lpsOriginalSigmaCombinationZSeries
  have hT : (1728:PowerSeries ℚ)*T=720*A+1008*B := by
    rw [show T=PowerSeries.C (12:ℚ)⁻¹*(PowerSeries.C 5*A+PowerSeries.C 7*B) from
      lpsOriginalSigmaCombinationZSeries_map]
    change PowerSeries.C (1728:ℚ)*(PowerSeries.C (12:ℚ)⁻¹*(PowerSeries.C 5*A+PowerSeries.C 7*B))=_
    rw [←mul_assoc,←map_mul]
    norm_num [map_ofNat]
    ring
  have hden : (1728:PowerSeries ℚ)≠0 := by
    intro h
    have hc:=congrArg (PowerSeries.constantCoeff : PowerSeries ℚ→+*ℚ) h
    norm_num [map_ofNat] at hc
  apply mul_left_cancel₀ hden
  have hr : (1728:PowerSeries ℚ)*lpsOriginalDeltaQSeries=
      (lpsOriginalEisensteinQSeries 4)^3-(lpsOriginalEisensteinQSeries 6)^2 := by
    unfold lpsOriginalDeltaQSeries
    change PowerSeries.C (1728:ℚ)*(PowerSeries.C (1728:ℚ)⁻¹*_) = _
    rw [←mul_assoc,←map_mul]
    norm_num
  rw [hr,lpsOriginalE4QSeries_sigma,lpsOriginalE6QSeries_sigma]
  simp only [lpsOriginalDeltaZSeries,map_add,map_sub,map_mul,map_pow,PowerSeries.map_C]
  change (1728:PowerSeries ℚ)*(T+100*A^2-147*B^2+8000*A^3)=(1+240*A)^3-(1-504*B)^2
  calc
    _=1728*T+172800*A^2-254016*B^2+13824000*A^3 := by ring
    _=(1+240*A)^3-(1-504*B)^2 := by rw [hT];ring
end QEC.Coding.TannerLiftedProduct
