-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalInteriorForgetLevel_projection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:27:27.288802+00:00
-- url     : https://prove2.me/submissions/b62abb7e-b8bc-47d0-b4d3-358c4da2efc1

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
    lpsOriginalInteriorForgetLevel N M hNM ⟦τ⟧ = ⟦τ⟧ := rfl
end QEC.Coding.TannerLiftedProduct
