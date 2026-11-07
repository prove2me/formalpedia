-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalAnalyticCuspLocalizedNomeEval_invParameter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:42:12.188331+00:00
-- url     : https://prove2.me/submissions/2a4af7b5-0b39-4d23-a7de-2c3a56608401

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspSeriesReduction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAnalyticCuspLocalization
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAnalyticCuspLocalizedNomeEval_function

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (τ : ℍ) :
    lpsOriginalAnalyticCuspLocalizedNomeEval τ
      (IsLocalization.Away.invSelf (S:=lpsOriginalAnalyticCuspLaurentRing)
        lpsOriginalAnalyticCuspLaurentParameter)=
      (Function.Periodic.qParam 1 (τ:ℂ))⁻¹ := by
  have h:=congrArg (lpsOriginalAnalyticCuspLocalizedNomeEval τ)
    (IsLocalization.Away.mul_invSelf (S:=lpsOriginalAnalyticCuspLaurentRing)
      lpsOriginalAnalyticCuspLaurentParameter)
  rw [map_mul,map_one,lpsOriginalAnalyticCuspLocalizedNomeEval_function] at h
  change Function.Periodic.qParam 1 (τ:ℂ)*
    lpsOriginalAnalyticCuspLocalizedNomeEval τ
      (IsLocalization.Away.invSelf (S:=lpsOriginalAnalyticCuspLaurentRing)
        lpsOriginalAnalyticCuspLaurentParameter)=1 at h
  apply (mul_left_cancel₀ (Function.Periodic.qParam_ne_zero (τ:ℂ)))
  rw [h,mul_inv_cancel₀ (Function.Periodic.qParam_ne_zero (τ:ℂ))]
end QEC.Coding.TannerLiftedProduct
