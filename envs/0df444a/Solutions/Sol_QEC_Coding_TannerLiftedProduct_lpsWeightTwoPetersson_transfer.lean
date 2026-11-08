-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsWeightTwoPetersson_transfer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:20:33.111266+00:00
-- url     : https://prove2.me/submissions/091dc06a-021c-47eb-a364-bc3a3c937ef4

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularFundamentalDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonDomainTransfer
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHorocyclePoint_im
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHorocyclePoint_im



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (f g : ℍ → ℂ) (A : GL (Fin 2) ℝ)
    (hA : 0 < A.det.val) (τ : ℍ) :
    petersson 2 (f ∣[(2 : ℤ)] A) g τ = petersson 2 f (g ∣[(2 : ℤ)] A⁻¹) (A • τ) := by
  have he := UpperHalfPlane.petersson_slash 2 f (g ∣[(2 : ℤ)] A⁻¹) A τ
  have hA' : 0 < (A : Matrix (Fin 2) (Fin 2) ℝ).det := hA
  simpa [←SlashAction.slash_mul, UpperHalfPlane.σ,hA'] using he
end QEC.Coding.TannerLiftedProduct
