-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.tendsto_lpsStandardTheta_slash_pos_c
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:28:48.805205+00:00
-- url     : https://prove2.me/submissions/0698fb80-df96-4a34-9922-892e6e83b36d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsStandardTheta_slash_pos_c
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_tendsto_lpsThetaGaussSum_affine
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) (hq : 0<q) (γ : SL(2,ℤ)) (hc : 0<γ 1 0) :
    Tendsto (((fun w : UpperHalfPlane => lpsStandardTheta q w) ∣[(2:ℤ)] γ))
      UpperHalfPlane.atImInfty
      (𝓝 (-(32*(q:ℂ)^3*((γ 1 0).toNat:ℂ)^2)⁻¹ *
        lpsUnaryQuadraticGauss (γ 0 0) (γ 1 0).toNat *
        lpsUnaryQuadraticGauss (4*(q:ℤ)^2*γ 0 0) (γ 1 0).toNat ^3)) := by
  have h1 := tendsto_lpsThetaGaussSum_affine (γ 0 0) (γ 1 0).toNat 2
    ((γ 1 1:ℝ)/(γ 1 0:ℝ)) (by norm_num)
  have h8 := tendsto_lpsThetaGaussSum_affine (4*(q:ℤ)^2*γ 0 0) (γ 1 0).toNat
    (8*(q:ℝ)^2) ((γ 1 1:ℝ)/(γ 1 0:ℝ)) (by positivity)
  have h := (h1.mul (h8.pow 3)).const_mul (-(32*(q:ℂ)^3*((γ 1 0).toNat:ℂ)^2)⁻¹)
  simp only [Complex.ofReal_div,Complex.ofReal_intCast,Complex.ofReal_mul,Complex.ofReal_ofNat,
    Complex.ofReal_pow,Complex.ofReal_natCast] at h
  have he : ((fun w : UpperHalfPlane => lpsStandardTheta q w) ∣[(2:ℤ)] γ)=
      (fun z : UpperHalfPlane => -(32*(q:ℂ)^3*((γ 1 0).toNat:ℂ)^2)⁻¹ *
        lpsThetaGaussSum (γ 0 0) (γ 1 0).toNat (((z:ℂ)+(γ 1 1:ℂ)/(γ 1 0:ℂ))/2) *
        lpsThetaGaussSum (4*(q:ℤ)^2*γ 0 0) (γ 1 0).toNat
          (((z:ℂ)+(γ 1 1:ℂ)/(γ 1 0:ℂ))/(8*(q:ℂ)^2))^3) := by
    funext z
    exact lpsStandardTheta_slash_pos_c q hq γ hc z
  rw [he]
  simpa only [mul_assoc] using h
end QEC.Coding.TannerLiftedProduct
