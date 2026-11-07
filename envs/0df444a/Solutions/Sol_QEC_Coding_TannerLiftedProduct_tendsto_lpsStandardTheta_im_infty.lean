-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.tendsto_lpsStandardTheta_im_infty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:45:21.919083+00:00
-- url     : https://prove2.me/submissions/f0335264-7907-4697-b077-25a0bf5cade5

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAnalyticTheta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.ModularForms.Identities
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaS
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_tendsto_jacobiTheta_mul_im_infty

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) (hq : 0 < q) :
    Tendsto (fun z : UpperHalfPlane => lpsStandardTheta q z)
      UpperHalfPlane.atImInfty (𝓝 1) := by
  have h2 := tendsto_jacobiTheta_mul_im_infty 2 (by norm_num)
  have h8 := tendsto_jacobiTheta_mul_im_infty (8*(q:ℝ)^2) (by positivity)
  have h := h2.mul (h8.pow 3)
  norm_num only [Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.ofReal_pow,
    Complex.ofReal_natCast,one_pow,mul_one] at h
  apply h.congr
  intro z
  unfold lpsStandardTheta lpsAnalyticThetaProduct
  have he : (((2*q)^2 : ℕ):ℂ)*(2*(z:ℂ)) = 8*(q:ℂ)^2*(z:ℂ) := by
    push_cast
    ring
  rw [he]
end QEC.Coding.TannerLiftedProduct
