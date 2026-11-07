-- Prove2me | solution 1 for P2M_QEC_Coding_TannerLiftedProduct_jacobiTheta__term_norm_real_left_01b00fc6396f
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:43:16.158209+00:00
-- url     : https://prove2.me/submissions/f7a6df97-00ac-4d18-b26d-dd61298facfc

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaS
import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics
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
theorem _root_.solution (n : ℤ) (a : ℝ) (z : ℂ) :
    ‖jacobiTheta₂_term n (a:ℂ) z‖=‖Complex.exp ((Real.pi:ℂ)*Complex.I*(n:ℂ)^2*z)‖ := by
  rw [jacobiTheta₂_term,Complex.exp_add,norm_mul]
  have he : ‖Complex.exp (2*(Real.pi:ℂ)*Complex.I*(n:ℂ)*(a:ℂ))‖=1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re,Complex.mul_im]
  rw [he,one_mul]
end QEC.Coding.TannerLiftedProduct
