-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsTheta_mobius_scaled
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:24:52.691023+00:00
-- url     : https://prove2.me/submissions/b0159803-9e93-4b02-988b-face28120e79

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsTheta_rational_S
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_scaled_half_factor
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (a b d : ℤ) (c s : ℕ) [NeZero c] (hs : 0<s)
    (hdet : a*d-b*(c:ℤ)=1) (z : ℂ) (hz : 0<z.im) :
    jacobiTheta (2*(s:ℂ)*(((a:ℂ)*z+(b:ℂ))/((c:ℂ)*z+(d:ℂ)))) =
      (-Complex.I*((z+(d:ℂ)/(c:ℂ))/(2*(s:ℂ))))^(1/2:ℂ) *
        lpsThetaGaussSum ((s:ℤ)*a) c ((z+(d:ℂ)/(c:ℂ))/(2*(s:ℂ))) := by
  have hcR : 0<(c:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne c)
  have hc : (c:ℂ)≠0 := by exact_mod_cast NeZero.ne c
  have hsR : 0<(s:ℝ) := by exact_mod_cast hs
  have hs0 : (s:ℂ)≠0 := by exact_mod_cast ne_of_gt hs
  have hden : (c:ℂ)*z+(d:ℂ)≠0 := by
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.add_im,Complex.mul_im,Complex.natCast_re,Complex.natCast_im,
      Complex.intCast_im,zero_mul,add_zero,Complex.zero_im] at hi
    exact (mul_pos hcR hz).ne' hi
  have hden' : z*(c:ℂ)+(d:ℂ)≠0 := by simpa only [mul_comm z (c:ℂ)] using hden
  have hd : (a:ℂ)*(d:ℂ)-(b:ℂ)*(c:ℂ)=1 := by exact_mod_cast hdet
  have hphi : ((a:ℂ)*z+(b:ℂ))/((c:ℂ)*z+(d:ℂ)) =
      (a:ℂ)/(c:ℂ)-1/((c:ℂ)*((c:ℂ)*z+(d:ℂ))) := by
    field_simp [hc,hden,hden']
    linear_combination -hd
  let u := (z+(d:ℂ)/(c:ℂ))/(2*(s:ℂ))
  have hu : 0<u.im := by
    dsimp [u]
    rw [show 2*(s:ℂ)=((2*(s:ℝ):ℝ):ℂ) by push_cast;rfl,Complex.div_ofReal_im]
    simp only [Complex.add_im,Complex.div_im,Complex.intCast_im,Complex.natCast_im,
      mul_zero,zero_mul,sub_self,zero_div,add_zero]
    exact div_pos hz (by positivity)
  have hu0 : u≠0 := by
    apply ne_of_apply_ne Complex.im
    simpa only [Complex.zero_im] using ne_of_gt hu
  have hbig : 0<((c:ℂ)^2*u).im := by
    rw [← Complex.ofReal_natCast,← Complex.ofReal_pow,Complex.mul_im]
    simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
    exact mul_pos (sq_pos_of_pos hcR) hu
  have harg : 2*(s:ℂ)*(((a:ℂ)*z+(b:ℂ))/((c:ℂ)*z+(d:ℂ))) =
      -1/((c:ℂ)^2*u)+2*(((s:ℤ)*a:ℤ):ℂ)/(c:ℂ) := by
    rw [hphi]
    dsimp [u]
    push_cast
    field_simp [hc,hs0,hden]
    ring
  rw [harg,lpsTheta_rational_S ((s:ℤ)*a) c ((c:ℂ)^2*u) hbig]
  have hf := scaled_half_factor (c:ℝ) hcR (-Complex.I*u)
    (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hu0)
  simp only [Complex.ofReal_natCast] at hf
  have he : -Complex.I*((c:ℂ)^2*u)=(c:ℂ)^2*(-Complex.I*u) := by ring
  rw [he,hf]
  have hdv : ((c:ℂ)^2*u)/(c:ℂ)^2=u := by field_simp
  simp only [hdv]
  rw [mul_div_cancel_left₀ _ hc]
  rfl
end QEC.Coding.TannerLiftedProduct
