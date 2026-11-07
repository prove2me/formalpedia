-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.tendsto_lpsThetaGaussSum_affine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:57:00.283676+00:00
-- url     : https://prove2.me/submissions/bdbec0ae-be89-49ad-8790-a398a3a31419

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaS
import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics
import Theorems.Thm_P2M_QEC_Coding_TannerLiftedProduct_tendsto_jacobiTheta__real_affine_f3bbd6d1b908
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real Filter Topology
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (a : ℤ) (c : ℕ) (t d : ℝ) (ht : 0<t) :
    Tendsto (fun z : UpperHalfPlane => lpsThetaGaussSum a c (((z:ℂ)+(d:ℂ))/(t:ℂ)))
      UpperHalfPlane.atImInfty (𝓝 (lpsUnaryQuadraticGauss a c)) := by
  unfold lpsThetaGaussSum lpsUnaryQuadraticGauss
  have h := tendsto_finsetSum Finset.univ (fun (r : Fin c) hr =>
    (tendsto_jacobiTheta₂_real_affine ((r.val:ℝ)/(c:ℝ)) t d ht).const_mul (lpsQuadraticPhase a c r))
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,mul_one] using h
end QEC.Coding.TannerLiftedProduct
