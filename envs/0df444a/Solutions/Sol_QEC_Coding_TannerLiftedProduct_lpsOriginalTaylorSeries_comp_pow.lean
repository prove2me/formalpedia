-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalTaylorSeries_comp_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:56:34.430501+00:00
-- url     : https://prove2.me/submissions/759d1739-9a84-4155-bfc0-52056aa9d477

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
theorem _root_.solution {f : ℂ→ℂ} (hf : AnalyticAt ℂ f 0)
    (N : ℕ) (hN : N≠0) :
    lpsOriginalTaylorSeries (fun q => f (q^N))=
      PowerSeries.expand N hN (lpsOriginalTaylorSeries f) := by
  let S := PowerSeries.expand N hN (lpsOriginalTaylorSeries f)
  have ht : Filter.Tendsto (fun q : ℂ => q^N) (𝓝 0) (𝓝 0) := by
    have he : (id : ℂ→ℂ)^N=(fun q : ℂ=>q^N) := by
      ext q
      simp only [Pi.pow_apply,id_eq]
    have h := ((continuousAt_id : ContinuousAt (id : ℂ→ℂ) 0).pow N).tendsto
    rw [he] at h
    simpa only [zero_pow hN] using h
  have he := hasFPowerSeriesAt_iff.mp hf.hasFPowerSeriesAt
  have hex : HasFPowerSeriesAt (fun q : ℂ=>f (q^N))
      (FormalMultilinearSeries.ofScalars ℂ (fun n=>S.coeff n)) 0 := by
    apply hasFPowerSeriesAt_iff.mpr
    filter_upwards [ht.eventually he] with q hq
    simp only [zero_add,FormalMultilinearSeries.coeff_ofScalars] at hq ⊢
    have hinj : Function.Injective (fun n : ℕ => N*n) := by
      intro a b h
      exact Nat.mul_left_cancel (Nat.pos_of_ne_zero hN) h
    apply (hinj.hasSum_iff (fun n hn=> ?_)).mp
    · simpa only [Function.comp_def,S,PowerSeries.coeff_expand_mul,
        lpsOriginalTaylorSeries_coeff,pow_mul,smul_eq_mul,div_eq_mul_inv,mul_comm] using hq
    · have hn' : ¬N∣n := by
        intro hd
        obtain ⟨m,hm⟩ := hd
        exact hn ⟨m,hm.symm⟩
      simp only [S,PowerSeries.coeff_expand_of_not_dvd N hN _ hn',smul_zero]
  have h := hex.eq_formalMultilinearSeries hex.analyticAt.hasFPowerSeriesAt
  ext n
  have heq := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ=>p.coeff n) h
  simpa only [FormalMultilinearSeries.coeff_ofScalars,lpsOriginalTaylorSeries_coeff,
    div_eq_mul_inv,mul_comm] using heq.symm
end QEC.Coding.TannerLiftedProduct
