-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsShiftedTheta_S
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:42:30.312067+00:00
-- url     : https://prove2.me/submissions/61aa72d0-e2a6-4e8c-bc22-8c1328b86451

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
theorem _root_.solution (a z : ℂ) (hz : 0<z.im) :
    lpsShiftedTheta a (-1/z)=(-Complex.I*z)^(1/2:ℂ)*jacobiTheta₂ a z := by
  have hz0 : z≠0 := by intro he;subst z;simp at hz
  have hb : -Complex.I*z≠0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hz0
  have hp : (-Complex.I*z)^(1/2:ℂ)≠0 := (Complex.cpow_ne_zero_iff).mpr (Or.inl hb)
  have h := congrArg (fun w => (-Complex.I*z)^(1/2:ℂ)*w) (jacobiTheta₂_functional_equation a z)
  have he : lpsShiftedTheta a (-1/z)=
      Complex.exp (-(Real.pi:ℂ)*Complex.I*a^2/z)*jacobiTheta₂ (a/z) (-1/z) := by
    unfold lpsShiftedTheta
    have ha : a*(-1/z)=-(a/z) := by ring
    rw [ha,jacobiTheta₂_neg_left]
    congr 2
    ring
  rw [he]
  field_simp [hp] at h
  simpa only [neg_mul,neg_div,mul_comm Complex.I (Real.pi:ℂ)] using h.symm
end QEC.Coding.TannerLiftedProduct
