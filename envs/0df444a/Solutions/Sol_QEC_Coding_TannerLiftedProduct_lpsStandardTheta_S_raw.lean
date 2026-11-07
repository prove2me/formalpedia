-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsStandardTheta_S_raw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:43:21.40521+00:00
-- url     : https://prove2.me/submissions/38dee10b-e5dd-4738-af1e-1917cea27570

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAnalyticTheta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.ModularForms.Identities
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaS
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_theta_scaled_S
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_scaled_half_factor
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) (hq : 0 < q) (z : ℂ) (hz : 0 < z.im) :
    lpsStandardTheta q (-1/z) = -(z^2 / (32*(q:ℂ)^3)) *
      jacobiTheta (z/2) * jacobiTheta (z/(8*(q:ℂ)^2))^3 := by
  have qn : (q : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hq
  have zn : z ≠ 0 := by intro h; simp [h] at hz
  have h8 : (0 : ℝ) < 8*(q:ℝ)^2 := mul_pos (by norm_num) (sq_pos_of_pos (by exact_mod_cast hq))
  have hs2 := theta_scaled_S 2 (by norm_num) z hz
  have hs8 := theta_scaled_S (8*(q:ℝ)^2) h8 z hz
  norm_num only [Complex.ofReal_ofNat,Complex.ofReal_mul,Complex.ofReal_pow,
    Complex.ofReal_natCast] at hs2 hs8
  have hz2 : -Complex.I * (z/2) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
    (div_ne_zero zn (by norm_num))
  have hf := scaled_half_factor (1/(2*(q:ℝ))) (by positivity) (-Complex.I*(z/2)) hz2
  have he : ((1/(2*(q:ℝ)) : ℝ):ℂ)^2 * (-Complex.I*(z/2)) =
      -Complex.I*(z/(8*(q:ℂ)^2)) := by
    push_cast
    field_simp
    ring
  rw [he] at hf
  unfold lpsStandardTheta lpsAnalyticThetaProduct
  have hh : (((2*q)^2 : ℕ):ℂ) * (2*(-1/z)) = (8*(q:ℂ)^2)*(-1/z) := by
    push_cast
    ring
  rw [hh,hs2,hs8,hf]
  have hfour : ((-Complex.I*(z/2))^(1/2 : ℂ))^4 = (-Complex.I*(z/2))^2 := by
    rw [show (4 : ℕ) = 2*2 by norm_num,pow_mul,show (1/2 : ℂ) = (2 : ℂ)⁻¹ by norm_num,Complex.cpow_ofNat_inv_pow]
  calc
    _ = (((-Complex.I*(z/2))^(1/2 : ℂ))^4) *
        (((1/(2*(q:ℝ)) : ℝ):ℂ)^3) * jacobiTheta (z/2) *
          jacobiTheta (z/(8*(q:ℂ)^2))^3 := by ring
    _ = _ := by
      rw [hfour]
      push_cast
      field_simp
      simp only [Complex.I_sq]
      ring
end QEC.Coding.TannerLiftedProduct
