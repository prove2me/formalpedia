-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJDilated_nonconstant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:05:14.144344+00:00
-- url     : https://prove2.me/submissions/94334076-cec0-4354-a3f9-b618de3d0fab

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJDilated_nonconstant

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) (hN : 0<N) :
    ¬∃ c : ℂ, ∀ x : LPSOriginalFilledCurve N, lpsOriginalFilledJDilated N hN x=c := by
  rintro ⟨c,hc⟩
  exact lpsOriginalJDilated_nonconstant N hN ⟨c,fun τ => hc (Sum.inl ⟦τ⟧)⟩
end QEC.Coding.TannerLiftedProduct
