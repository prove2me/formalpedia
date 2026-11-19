-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsTheta_rational_S
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:23:38.9852+00:00
-- url     : https://prove2.me/submissions/2c80bef6-7a23-4370-87c4-2f9310935b5e

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaS
import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsTheta_residue_expansion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsShiftedTheta_scaled_S
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
theorem _root_.solution (a : ℤ) (c : ℕ) [NeZero c] (z : ℂ) (hz : 0<z.im) :
    jacobiTheta (-1/z+2*(a:ℂ)/(c:ℂ))=
      ((-Complex.I*z)^(1/2:ℂ)/(c:ℂ)) *
        ∑ r : Fin c, lpsQuadraticPhase a c r * jacobiTheta₂ ((r.val:ℂ)/(c:ℂ)) (z/(c:ℂ)^2) := by
  have zn : z≠0 := by intro he;subst z;simp at hz
  have hi : 0<(-1/z).im := by
    simpa only [neg_div,one_div,Complex.neg_im,Complex.inv_im,neg_neg] using
      div_pos hz (Complex.normSq_pos.mpr zn)
  rw [lpsTheta_residue_expansion a c (-1/z) hi]
  simp_rw [lpsShiftedTheta_scaled_S _ z c hz]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  ring
end QEC.Coding.TannerLiftedProduct
