-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalAffineSmallerPoleLimit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:17:39.950819+00:00
-- url     : https://prove2.me/submissions/174dec35-3714-482b-b865-c2a04b16d7eb

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactStabilizer
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAffineNomeLimit
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAffinePolePullback
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJQCoefficient_analytic_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJQCoefficient_zero
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
theorem _root_.solution (m k : ℕ) (hm : 0<m)
    (hmk : m<k) (r : ℝ) :
    Tendsto (fun τ : ℍ=>Function.Periodic.qParam 1 (τ:ℂ)^k*
      lpsOriginalJInvariant (lpsE2AffineMatrix m hm r • τ))
      UpperHalfPlane.atImInfty (𝓝 0) := by
  have hq := (UpperHalfPlane.qParam_tendsto_atImInfty
    (by norm_num : (0:ℝ)<1)).pow (k-m)
  have hK := lpsOriginalJQCoefficient_analytic_zero.continuousAt.tendsto.comp
    (lpsOriginalAffineNomeLimit m hm r)
  have h := (hq.div_const (Function.Periodic.qParam 1 (r:ℂ))).mul hK
  rw [lpsOriginalJQCoefficient_zero] at h
  have hs : Tendsto (fun τ : ℍ=>Function.Periodic.qParam 1 (τ:ℂ)^(k-m)/
      Function.Periodic.qParam 1 (r:ℂ)*lpsOriginalJQCoefficient
        (Function.Periodic.qParam 1 ((lpsE2AffineMatrix m hm r • τ:ℍ):ℂ)))
      UpperHalfPlane.atImInfty (𝓝 0) := by
    simpa only [zero_pow (Nat.sub_pos_of_lt hmk).ne',zero_div,zero_mul,Function.comp_def] using h
  exact hs.congr fun τ=>(lpsOriginalAffinePolePullback m k hm hmk.le r τ).symm
end QEC.Coding.TannerLiftedProduct
