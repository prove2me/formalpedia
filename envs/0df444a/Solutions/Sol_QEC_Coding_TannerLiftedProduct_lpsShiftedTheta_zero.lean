-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsShiftedTheta_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:43:27.992194+00:00
-- url     : https://prove2.me/submissions/452bfe98-1700-4efb-a198-13933e94c47b

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
theorem _root_.solution (z : ℂ) : lpsShiftedTheta 0 z=jacobiTheta z := by
  simp [lpsShiftedTheta,jacobiTheta_eq_jacobiTheta₂]
end QEC.Coding.TannerLiftedProduct
