-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsThetaGaussSum_scalar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:57:01.679848+00:00
-- url     : https://prove2.me/submissions/9bc14b09-94ae-4b17-b430-5abca1dead81

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics
import Mathlib.Analysis.Fourier.ZMod
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaGaussSum_eq_quadraticFourier
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticFourier_even_support
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticFourier_det_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N s k : ℕ) [NeZero N] (hs : 0 < s) (hk : 0 < k)
    (hN : N=4*s*k) (a b d : ℤ) (hdet : a*d-b*(N:ℤ)=1)
    (z : ℂ) (hz : 0 < z.im) :
    lpsThetaGaussSum ((s:ℤ)*a) N ((z+(d:ℂ)/(N:ℂ))/(2*(s:ℂ))) =
      lpsUnaryQuadraticGauss ((s:ℤ)*a) N * jacobiTheta (2*(s:ℂ)*z) := by
  let w : ℂ := (z+(d:ℂ)/(N:ℂ))/(2*(s:ℂ))
  have hw : 0 < w.im := by
    dsimp [w]
    rw [show 2*(s:ℂ)=((2*(s:ℝ):ℝ):ℂ) by push_cast;rfl,Complex.div_ofReal_im]
    simp only [Complex.add_im,Complex.div_im,Complex.intCast_im,Complex.natCast_im,
      mul_zero,zero_mul,sub_self,zero_div,add_zero]
    exact div_pos hz (by positivity)
  rw [lpsThetaGaussSum_eq_quadraticFourier _ _ _ hw]
  let f : ℤ → ℂ := fun n => lpsQuadraticFourier N (((s:ℤ)*a:ℤ):ZMod N) (n:ZMod N) *
    Complex.exp ((Real.pi:ℂ)*Complex.I*(n:ℂ)^2*w)
  have hi : Function.Injective (fun j : ℤ => 2*(s:ℤ)*j) := by
    intro i j he
    exact mul_left_cancel₀ (by positivity : 2*(s:ℤ)≠0) he
  have hsupport : Function.support f ⊆ Set.range (fun j : ℤ => 2*(s:ℤ)*j) := by
    intro n hn
    by_contra hnr
    have hnd : ¬(2*(s:ℤ)) ∣ n := by
      rintro ⟨j,hj⟩
      exact hnr ⟨j,hj.symm⟩
    have he := lpsQuadraticFourier_even_support N s k hN hk a n hnd
    apply hn
    dsimp [f]
    rw [he,zero_mul]
  have hr := hi.tsum_eq (f:=f) hsupport
  change (∑' n : ℤ, f n)=_
  rw [← hr,jacobiTheta,← tsum_mul_left]
  apply tsum_congr
  intro j
  dsimp only [f]
  rw [lpsQuadraticFourier_det_even N s a b d j hdet,ZMod.stdAddChar_coe]
  have he :
      Complex.exp (2*(Real.pi:ℂ)*Complex.I*((-(s:ℤ)*d*j^2:ℤ):ℂ)/(N:ℂ)) *
        Complex.exp ((Real.pi:ℂ)*Complex.I*((2*(s:ℤ)*j:ℤ):ℂ)^2*w) =
      Complex.exp ((Real.pi:ℂ)*Complex.I*(j:ℂ)^2*(2*(s:ℂ)*z)) := by
    rw [← Complex.exp_add]
    congr 1
    dsimp [w]
    push_cast
    have sn : (s:ℂ)≠0 := by exact_mod_cast ne_of_gt hs
    have cn : (N:ℂ)≠0 := by exact_mod_cast NeZero.ne N
    field_simp [sn,cn]
    ring
  rw [mul_comm (Complex.exp _) (lpsUnaryQuadraticGauss _ _),mul_assoc,he]
end QEC.Coding.TannerLiftedProduct
