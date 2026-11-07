-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGamma0CompactCore_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:45:11.038196+00:00
-- url     : https://prove2.me/submissions/7ddb0922-9cd3-4db7-98b7-7415b77fe199

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspOrbits
import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.ProperlyDiscontinuous
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGamma0Projected_continuous

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (Y : ℝ) :
    IsCompact (lpsOriginalGamma0CompactCore N Y) := by
  apply isCompact_iUnion
  intro x
  exact (ModularGroup.isCompact_truncatedFundamentalDomain Y).image
    (lpsOriginalGamma0Projected_continuous N _)
end QEC.Coding.TannerLiftedProduct
