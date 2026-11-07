-- Prove2me | solution 1 for P2M_QEC_Coding_TannerLiftedProduct_hasSum_nat_jacobiTheta__real_cc862f55b35d
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:43:17.447449+00:00
-- url     : https://prove2.me/submissions/b2f29d6f-a02a-492b-a97d-0a268d0bfb8d

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
theorem _root_.solution (a : ℝ) (z : ℂ) (hz : 0<z.im) :
    HasSum (fun n : ℕ => jacobiTheta₂_term (n+1) (a:ℂ) z +
      jacobiTheta₂_term (-(n+1)) (a:ℂ) z) (jacobiTheta₂ (a:ℂ) z-1) := by
  have h := (hasSum_jacobiTheta₂_term (a:ℂ) hz).nat_add_neg
  rw [← hasSum_nat_add_iff' 1] at h
  convert! h using 1
  simp [jacobiTheta₂_term,sub_eq_add_neg]
end QEC.Coding.TannerLiftedProduct
