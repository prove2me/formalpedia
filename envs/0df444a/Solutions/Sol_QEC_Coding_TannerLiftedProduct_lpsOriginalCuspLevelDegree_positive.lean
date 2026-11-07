-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspLevelDegree_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:41:36.659885+00:00
-- url     : https://prove2.me/submissions/3c45319d-0666-4c24-90df-439ed60a001b

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspLevelDegree_mul_width
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspWidthNat_positive


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N M : ℕ) [NeZero N] [NeZero M]
    (hNM : N ∣ M) (ρ : SL(2, ℤ)) : 0 < lpsOriginalCuspLevelDegree N M ρ := by
  apply Nat.pos_of_ne_zero
  intro h
  have hm := lpsOriginalCuspLevelDegree_mul_width N M hNM ρ
  rw [h, mul_zero] at hm
  exact (Nat.ne_of_gt (lpsOriginalCuspWidthNat_positive M ρ)) hm.symm
end QEC.Coding.TannerLiftedProduct
