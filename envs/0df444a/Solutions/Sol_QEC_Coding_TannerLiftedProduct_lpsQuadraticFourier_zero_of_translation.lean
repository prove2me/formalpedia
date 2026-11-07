-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuadraticFourier_zero_of_translation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:45:13.758104+00:00
-- url     : https://prove2.me/submissions/1275dab6-1cb4-4214-9d27-ff9a38086718

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics
import Mathlib.Analysis.Fourier.ZMod
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier
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
theorem _root_.solution (N : ℕ) [NeZero N] (a n t : ZMod N)
    (hlinear : 2*a*t=0) (hquadratic : a*t^2=0) (hn : n*t≠0) :
    lpsQuadraticFourier N a n=0 := by
  have he : ZMod.stdAddChar (n*t)≠(1:ℂ) := by
    intro h
    apply hn
    exact ZMod.injective_stdAddChar (h.trans (AddChar.map_zero_eq_one _).symm)
  have hshift : ZMod.stdAddChar (n*t)*lpsQuadraticFourier N a n = lpsQuadraticFourier N a n := by
    unfold lpsQuadraticFourier
    rw [Finset.mul_sum]
    have h := Equiv.sum_comp (Equiv.addRight t) (fun r : ZMod N => ZMod.stdAddChar (a*r^2+n*r))
    rw [← h]
    apply Finset.sum_congr rfl
    intro r hr
    rw [← AddChar.map_add_eq_mul]
    simp only [Equiv.coe_addRight]
    congr 1
    linear_combination -r*hlinear-hquadratic
  by_contra hnzero
  exact he ((mul_eq_right₀ hnzero).mp hshift)
end QEC.Coding.TannerLiftedProduct
