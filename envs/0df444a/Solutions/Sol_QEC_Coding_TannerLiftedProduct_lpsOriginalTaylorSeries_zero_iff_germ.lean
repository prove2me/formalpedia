-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalTaylorSeries_zero_iff_germ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:56:24.513267+00:00
-- url     : https://prove2.me/submissions/4751f802-8d93-470c-9d33-a94e99a50841

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalQExpansionArithmetic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.PowerSeries.Expand
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
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
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution {f : ℂ→ℂ} (hf : AnalyticAt ℂ f 0) :
    lpsOriginalTaylorSeries f=0 ↔ f=ᶠ[𝓝 0]0 := by
  constructor
  · intro h
    have h0 : FormalMultilinearSeries.ofScalars ℂ
        (fun n=>iteratedDeriv n f 0/(n.factorial:ℂ))=0 := by
      funext n
      apply FormalMultilinearSeries.coeff_eq_zero.mp
      have he := congrArg (fun S : PowerSeries ℂ=>S.coeff n) h
      simpa only [FormalMultilinearSeries.coeff_ofScalars,lpsOriginalTaylorSeries_coeff,
        div_eq_mul_inv,mul_comm,map_zero] using he
    have hp := hf.hasFPowerSeriesAt
    rw [h0] at hp
    exact hp.eventually_eq_zero
  · intro h
    have hp := hf.hasFPowerSeriesAt.eq_zero_of_eventually h
    ext n
    have he := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ=>p.coeff n) hp
    have hz : (0 : FormalMultilinearSeries ℂ ℂ ℂ).coeff n=0 := rfl
    rw [hz] at he
    simpa only [FormalMultilinearSeries.coeff_ofScalars,lpsOriginalTaylorSeries_coeff,
      div_eq_mul_inv,mul_comm,map_zero] using he
end QEC.Coding.TannerLiftedProduct
