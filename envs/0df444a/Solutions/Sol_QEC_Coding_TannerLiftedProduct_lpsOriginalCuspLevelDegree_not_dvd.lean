-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspLevelDegree_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:05:54.077061+00:00
-- url     : https://prove2.me/submissions/647b5653-a336-4a83-a749-3a11b8c76a90

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspLevelDegree_dvd_level

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N M p : ℕ) [NeZero N] [NeZero M]
    (hNM : N ∣ M) (hpM : ¬p ∣ M) (ρ : SL(2, ℤ)) : ¬p ∣ lpsOriginalCuspLevelDegree N M ρ := by
  intro h
  exact hpM (h.trans (lpsOriginalCuspLevelDegree_dvd_level N M hNM ρ))
end QEC.Coding.TannerLiftedProduct
