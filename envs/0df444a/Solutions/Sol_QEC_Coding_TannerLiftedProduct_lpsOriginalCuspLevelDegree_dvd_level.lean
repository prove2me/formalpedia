-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspLevelDegree_dvd_level
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:41:47.304265+00:00
-- url     : https://prove2.me/submissions/5b600faa-3735-44ea-84bf-85f5129f129b

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspWidthNat_dvd_level
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspLevelDegree_mul_width

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N M : ℕ) [NeZero N] [NeZero M]
    (hNM : N ∣ M) (ρ : SL(2, ℤ)) : lpsOriginalCuspLevelDegree N M ρ ∣ M := by
  have h : lpsOriginalCuspLevelDegree N M ρ ∣ lpsOriginalCuspWidthNat M ρ := by
    refine ⟨lpsOriginalCuspWidthNat N ρ, ?_⟩
    rw [mul_comm]
    exact (lpsOriginalCuspLevelDegree_mul_width N M hNM ρ).symm
  exact h.trans (lpsOriginalCuspWidthNat_dvd_level M ρ)
end QEC.Coding.TannerLiftedProduct
