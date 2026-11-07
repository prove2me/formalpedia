-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.tendsto_lpsStandardTheta_slash_S
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:46:41.277566+00:00
-- url     : https://prove2.me/submissions/ac910abd-9162-489e-8383-eaae797e6722

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAnalyticTheta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.ModularForms.Identities
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaS
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsStandardTheta_slash_S
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_tendsto_jacobiTheta_div_im_infty

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) (hq : 0 < q) :
    Tendsto ((fun w : UpperHalfPlane => lpsStandardTheta q w) ∣[(2 : ℤ)] ModularGroup.S)
      UpperHalfPlane.atImInfty (𝓝 (-(32*(q:ℂ)^3)⁻¹)) := by
  have h2 := tendsto_jacobiTheta_div_im_infty 2 (by norm_num)
  have h8 := tendsto_jacobiTheta_div_im_infty (8*(q:ℝ)^2) (by positivity)
  have hc : Tendsto (fun _ : UpperHalfPlane => -(32*(q:ℂ)^3)⁻¹)
      UpperHalfPlane.atImInfty (𝓝 (-(32*(q:ℂ)^3)⁻¹)) := tendsto_const_nhds
  have h := (hc.mul h2).mul (h8.pow 3)
  norm_num only [Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.ofReal_pow,
    Complex.ofReal_natCast,one_pow,mul_one] at h
  exact h.congr (fun z => (lpsStandardTheta_slash_S q hq z).symm)
end QEC.Coding.TannerLiftedProduct
