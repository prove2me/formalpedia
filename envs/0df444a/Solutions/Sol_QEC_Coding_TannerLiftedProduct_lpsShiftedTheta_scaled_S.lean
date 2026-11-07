-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsShiftedTheta_scaled_S
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:43:41.441573+00:00
-- url     : https://prove2.me/submissions/3b57342b-3f80-421e-8505-8f0b68d80ad6

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaS
import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsShiftedTheta_S
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_scaled_half_factor
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real Filter Topology
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (a z : ℂ) (c : ℕ) [NeZero c] (hz : 0<z.im) :
    lpsShiftedTheta a ((c:ℂ)^2*(-1/z))=
      ((-Complex.I*z)^(1/2:ℂ)/(c:ℂ))*jacobiTheta₂ a (z/(c:ℂ)^2) := by
  have hcR : 0<(c:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne c)
  have hc : (c:ℂ)≠0 := by exact_mod_cast NeZero.ne c
  have hz0 : z≠0 := by intro he;subst z;simp at hz
  have hu : 0<(z/(c:ℂ)^2).im := by
    rw [← Complex.ofReal_natCast,← Complex.ofReal_pow,Complex.div_ofReal_im]
    exact div_pos hz (sq_pos_of_pos hcR)
  have h := lpsShiftedTheta_S a (z/(c:ℂ)^2) hu
  have ha : (c:ℂ)^2*(-1/z)=-1/(z/(c:ℂ)^2) := by field_simp
  rw [ha,h]
  have hb : -Complex.I*z≠0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hz0
  have hf := scaled_half_factor (1/(c:ℝ)) (by positivity) (-Complex.I*z) hb
  have he : ((1/(c:ℝ):ℝ):ℂ)^2*(-Complex.I*z)=-Complex.I*(z/(c:ℂ)^2) := by
    push_cast
    field_simp
  rw [he] at hf
  rw [hf]
  push_cast
  ring
end QEC.Coding.TannerLiftedProduct
