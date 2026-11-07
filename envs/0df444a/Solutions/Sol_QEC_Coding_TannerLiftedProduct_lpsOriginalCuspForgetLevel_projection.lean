-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspForgetLevel_projection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:06:47.42463+00:00
-- url     : https://prove2.me/submissions/636c0224-827c-420a-812f-e2c9edd6a6b5

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N M : ℕ) [NeZero N] [NeZero M]
    (hNM : N ∣ M) (ρ : SL(2, ℤ)) :
    lpsOriginalCuspForgetLevel N M hNM (lpsOriginalCuspOrbit M ρ) = lpsOriginalCuspOrbit N ρ := by
  rw [lpsOriginalCuspOrbit, lpsOriginalCuspOrbit, cosetToCuspOrbit_apply_mk,
    cosetToCuspOrbit_apply_mk]
  rfl
end QEC.Coding.TannerLiftedProduct
