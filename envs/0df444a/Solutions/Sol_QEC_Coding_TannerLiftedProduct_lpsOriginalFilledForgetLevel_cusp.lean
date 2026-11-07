-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledForgetLevel_cusp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:28:34.039134+00:00
-- url     : https://prove2.me/submissions/e3ebf1e0-1a3c-4d23-a2b4-6a0b7c30487e

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspForgetLevel_projection

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N M : ℕ) [NeZero N] [NeZero M]
    (hNM : N ∣ M) (ρ : SL(2, ℤ)) :
    lpsOriginalFilledForgetLevel N M hNM (Sum.inr (lpsOriginalCuspOrbit M ρ)) =
      Sum.inr (lpsOriginalCuspOrbit N ρ) := by
  exact congrArg Sum.inr (lpsOriginalCuspForgetLevel_projection N M hNM ρ)
end QEC.Coding.TannerLiftedProduct
