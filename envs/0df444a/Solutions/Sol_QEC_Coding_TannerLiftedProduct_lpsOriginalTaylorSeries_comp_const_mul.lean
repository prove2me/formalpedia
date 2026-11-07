-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalTaylorSeries_comp_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:08:11.534997+00:00
-- url     : https://prove2.me/submissions/240f2d89-ace6-4381-8a65-a6c74750d7b5

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
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_coeff
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
theorem _root_.solution
    {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (c : ℂ) :
    lpsOriginalTaylorSeries (fun q => f (c*q)) =
      PowerSeries.rescale c (lpsOriginalTaylorSeries f) := by
  let S := PowerSeries.rescale c (lpsOriginalTaylorSeries f)
  have ht : Tendsto (fun q : ℂ => c*q) (𝓝 0) (𝓝 0) := by
    simpa only [mul_zero, id_eq] using
      (tendsto_const_nhds (x := c)).mul (tendsto_id : Tendsto (id : ℂ → ℂ) (𝓝 0) (𝓝 0))
  have he := hasFPowerSeriesAt_iff.mp hf.hasFPowerSeriesAt
  have hex : HasFPowerSeriesAt (fun q : ℂ => f (c*q))
      (FormalMultilinearSeries.ofScalars ℂ (fun n => S.coeff n)) 0 := by
    apply hasFPowerSeriesAt_iff.mpr
    filter_upwards [ht.eventually he] with q hq
    simp only [zero_add, FormalMultilinearSeries.coeff_ofScalars] at hq ⊢
    convert hq using 1
    funext n
    simp only [S, PowerSeries.coeff_rescale, lpsOriginalTaylorSeries_coeff,
      smul_eq_mul]
    ring
  have h := hex.eq_formalMultilinearSeries hex.analyticAt.hasFPowerSeriesAt
  ext n
  have heq := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) h
  simpa only [FormalMultilinearSeries.coeff_ofScalars, lpsOriginalTaylorSeries_coeff,
    div_eq_mul_inv, mul_comm] using heq.symm
end QEC.Coding.TannerLiftedProduct
