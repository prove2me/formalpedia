-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledForgetLevel_projection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:19:32.17082+00:00
-- url     : https://prove2.me/submissions/d10d05bb-bd0b-40a1-a866-0e1b1bd20406

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N M : ℕ) (hNM : N ∣ M) (τ : ℍ) :
    lpsOriginalFilledForgetLevel N M hNM (Sum.inl ⟦τ⟧) = Sum.inl ⟦τ⟧ := rfl
end QEC.Coding.TannerLiftedProduct
