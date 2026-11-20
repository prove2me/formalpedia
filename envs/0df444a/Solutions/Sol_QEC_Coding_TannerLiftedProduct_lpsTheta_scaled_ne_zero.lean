-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsTheta_scaled_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:05:31.168494+00:00
-- url     : https://prove2.me/submissions/cbdca2f3-5e61-4241-b636-7e8c4082e7e1

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspIntegralHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaPeterssonPositive
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaIntegralLattice
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaIntegerDenominator_ne_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaCuspidalRemainder_ne_zero


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Polynomial
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) :
    lpsThetaIntegerDenominator q • lpsThetaCuspidalRemainder q hq4 ≠ 0 := by
  rw [← Int.cast_smul_eq_zsmul ℂ]
  have hd : (lpsThetaIntegerDenominator q : ℂ)≠0 := by
    exact_mod_cast lpsThetaIntegerDenominator_ne_zero q
  exact smul_ne_zero hd (lpsThetaCuspidalRemainder_ne_zero q hq4)
end QEC.Coding.TannerLiftedProduct
