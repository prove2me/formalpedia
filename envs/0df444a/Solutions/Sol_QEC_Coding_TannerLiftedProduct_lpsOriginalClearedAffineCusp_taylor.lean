-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalClearedAffineCusp_taylor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:21:24.527473+00:00
-- url     : https://prove2.me/submissions/6b5f4b43-19c2-4295-8610-2d6f82ffc285

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactFunctionFieldDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactStabilizer
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerQExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.Minpoly
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJQCoefficient_analytic_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPower_analytic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_const_mul
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_mul
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_qpow
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
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (B m : ℕ) (hm : m≠0) (r : ℚ) :
    lpsOriginalTaylorSeries (lpsOriginalClearedAffineCusp B m r)=
      PowerSeries.C ((Function.Periodic.qParam 1 (r:ℂ))⁻¹) *
        (PowerSeries.X^(B-m)*lpsOriginalTaylorSeries
          (fun q : ℂ=>lpsOriginalJQCoefficient
            (Function.Periodic.qParam 1 (r:ℂ)*q^m))) := by
  have hf : AnalyticAt ℂ (fun q : ℂ=>lpsOriginalJQCoefficient
      (Function.Periodic.qParam 1 (r:ℂ)*q^m)) 0 :=
    lpsOriginalJQCoefficient_analytic_zero.fun_comp_of_eq
      (analyticAt_const.mul (lpsOriginalPower_analytic m)) (by simp [hm])
  have he : lpsOriginalClearedAffineCusp B m r=
      fun q : ℂ=>(Function.Periodic.qParam 1 (r:ℂ))⁻¹ *
        (q^(B-m)*lpsOriginalJQCoefficient (Function.Periodic.qParam 1 (r:ℂ)*q^m)) := by
    funext q
    dsimp only [lpsOriginalClearedAffineCusp]
    ring
  rw [he,lpsOriginalTaylorSeries_const_mul]
  change PowerSeries.C _ * lpsOriginalTaylorSeries
    ((fun q : ℂ=>q^(B-m)) * (fun q : ℂ=>lpsOriginalJQCoefficient
      (Function.Periodic.qParam 1 (r:ℂ)*q^m))) = _
  rw [lpsOriginalTaylorSeries_mul (lpsOriginalPower_analytic _) hf,
    lpsOriginalTaylorSeries_qpow]
end QEC.Coding.TannerLiftedProduct
