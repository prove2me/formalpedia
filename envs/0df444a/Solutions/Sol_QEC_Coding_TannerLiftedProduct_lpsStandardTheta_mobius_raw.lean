-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsStandardTheta_mobius_raw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:26:20.82003+00:00
-- url     : https://prove2.me/submissions/f91dc2bd-c722-410e-8e9b-b3c422c46d0b

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsTheta_mobius_scaled
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_scaled_half_factor
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) (hq : 0<q) (a b d : ℤ) (c : ℕ) [NeZero c]
    (hdet : a*d-b*(c:ℤ)=1) (z : ℂ) (hz : 0<z.im) :
    lpsStandardTheta q (((a:ℂ)*z+(b:ℂ))/((c:ℂ)*z+(d:ℂ))) =
      -((z+(d:ℂ)/(c:ℂ))^2/(32*(q:ℂ)^3)) *
        lpsThetaGaussSum a c ((z+(d:ℂ)/(c:ℂ))/2) *
        lpsThetaGaussSum (4*(q:ℤ)^2*a) c ((z+(d:ℂ)/(c:ℂ))/(8*(q:ℂ)^2))^3 := by
  have qn : (q:ℂ)≠0 := by exact_mod_cast ne_of_gt hq
  have h2 := lpsTheta_mobius_scaled a b d c 1 (by norm_num) hdet z hz
  norm_num only [Nat.cast_one,mul_one,one_mul,Int.cast_ofNat] at h2
  have h8 := lpsTheta_mobius_scaled a b d c (4*q^2) (by positivity) hdet z hz
  norm_num only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow] at h8
  rw [show (2:ℂ)*(4*(q:ℂ)^2)=8*(q:ℂ)^2 by ring] at h8
  let w := z+(d:ℂ)/(c:ℂ)
  have hw : 0<w.im := by
    simpa [w,Complex.div_im] using hz
  have wn : w≠0 := by
    apply ne_of_apply_ne Complex.im
    simpa only [Complex.zero_im] using ne_of_gt hw
  have hn2 : -Complex.I*(w/2)≠0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
    (div_ne_zero wn (by norm_num))
  have hf := scaled_half_factor (1/(2*(q:ℝ))) (by positivity) (-Complex.I*(w/2)) hn2
  have he : ((1/(2*(q:ℝ)):ℝ):ℂ)^2*(-Complex.I*(w/2))=-Complex.I*(w/(8*(q:ℂ)^2)) := by
    push_cast
    field_simp
    ring
  rw [he] at hf
  unfold lpsStandardTheta lpsAnalyticThetaProduct
  have harg : (((2*q)^2:ℕ):ℂ)*(2*(((a:ℂ)*z+(b:ℂ))/((c:ℂ)*z+(d:ℂ)))) =
      (8*(q:ℂ)^2)*(((a:ℂ)*z+(b:ℂ))/((c:ℂ)*z+(d:ℂ))) := by push_cast;ring
  rw [harg,h2,h8]
  change (-Complex.I*(w/2))^(1/2:ℂ)*lpsThetaGaussSum a c (w/2)*
      ((-Complex.I*(w/(8*(q:ℂ)^2)))^(1/2:ℂ)*lpsThetaGaussSum (4*(q:ℤ)^2*a) c (w/(8*(q:ℂ)^2)))^3 = _
  rw [hf]
  have hfour : ((-Complex.I*(w/2))^(1/2:ℂ))^4=(-Complex.I*(w/2))^2 := by
    rw [show (4:ℕ)=2*2 by norm_num,pow_mul,show (1/2:ℂ)=(2:ℂ)⁻¹ by norm_num,
      Complex.cpow_ofNat_inv_pow]
  calc
    _ = ((-Complex.I*(w/2))^(1/2:ℂ))^4 * (((1/(2*(q:ℝ)):ℝ):ℂ)^3) *
        lpsThetaGaussSum a c (w/2)*lpsThetaGaussSum (4*(q:ℤ)^2*a) c (w/(8*(q:ℂ)^2))^3 := by ring
    _ = _ := by
      rw [hfour]
      push_cast
      field_simp
      simp only [Complex.I_sq]
      ring
end QEC.Coding.TannerLiftedProduct
