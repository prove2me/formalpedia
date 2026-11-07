-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspLevelDegree_mul_width
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:38:06.270047+00:00
-- url     : https://prove2.me/submissions/0cf580d0-3a7b-4626-b636-49f5e58ede28

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspWidthNat_dvd_of_level_dvd

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N M : ℕ) [NeZero N] [NeZero M]
    (hNM : N ∣ M) (ρ : SL(2, ℤ)) :
    lpsOriginalCuspWidthNat N ρ * lpsOriginalCuspLevelDegree N M ρ =
      lpsOriginalCuspWidthNat M ρ :=
  Nat.mul_div_cancel' (lpsOriginalCuspWidthNat_dvd_of_level_dvd N M hNM ρ)
end QEC.Coding.TannerLiftedProduct
