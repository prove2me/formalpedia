-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsStandardTheta_slash_level_fourth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:30:08.851203+00:00
-- url     : https://prove2.me/submissions/36a1b953-106f-4ae6-9582-1c8006ad2800

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaGaussScalar
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaGaussFourthReduction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaPositiveGaussScalar_eq_fourth
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsStandardTheta_slash_level_scalar


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real
open scoped UpperHalfPlane ModularForm MatrixGroups
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) (hq : 0 < q) (γ : SL(2,ℤ))
    (hc : 0 < γ 1 0) (hlevel : 16*q^2 ∣ (γ 1 0).toNat) (z : UpperHalfPlane) :
    ((fun w : UpperHalfPlane => lpsStandardTheta q w) ∣[(2:ℤ)] γ) z =
      (-(4*((γ 1 0).toNat:ℂ)^2)⁻¹ *
        lpsUnaryQuadraticGauss (γ 0 0) (γ 1 0).toNat^4) * lpsStandardTheta q z := by
  have h := lpsStandardTheta_slash_level_scalar q hq γ hc hlevel z
  change _ = lpsThetaPositiveGaussScalar q γ*lpsStandardTheta q z at h
  rw [lpsThetaPositiveGaussScalar_eq_fourth q hq γ hc hlevel] at h
  exact h
end QEC.Coding.TannerLiftedProduct
