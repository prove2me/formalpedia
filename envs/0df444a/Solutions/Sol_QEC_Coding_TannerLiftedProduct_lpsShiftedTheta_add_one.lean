-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsShiftedTheta_add_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:43:29.085662+00:00
-- url     : https://prove2.me/submissions/b20c407e-a190-4c3a-95c5-0eb4fe5642dd

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaS
import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsShiftedTheta_eq_tsum
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
theorem _root_.solution (a z : ℂ) : lpsShiftedTheta (a+1) z=lpsShiftedTheta a z := by
  rw [lpsShiftedTheta_eq_tsum,lpsShiftedTheta_eq_tsum]
  conv_rhs => rw [← (Equiv.addRight (1:ℤ)).tsum_eq]
  apply tsum_congr
  intro n
  simp only [Equiv.coe_addRight,Int.cast_add,Int.cast_one]
  congr 1
  ring
end QEC.Coding.TannerLiftedProduct
