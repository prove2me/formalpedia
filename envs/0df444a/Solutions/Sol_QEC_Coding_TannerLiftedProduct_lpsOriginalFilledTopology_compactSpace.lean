-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledTopology_compactSpace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:51:45.857779+00:00
-- url     : https://prove2.me/submissions/39d1b233-7855-4001-857f-44cfc5fd3c51

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
import Mathlib.Topology.Bases
import Mathlib.Topology.Order
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledTopology
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledTopology_interior_continuous
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledTopology_closedPatch_isCompact
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCurve_finite_cover
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGamma0CompactCore_isCompact


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] :
    @CompactSpace (LPSOriginalFilledCurve N) (lpsOriginalFilledTopology N) := by
  let := lpsOriginalFilledTopology N
  constructor
  rw [←lpsOriginalFilledCurve_finite_cover N]
  exact ((lpsOriginalGamma0CompactCore_isCompact N 2).image
    (lpsOriginalFilledTopology_interior_continuous N)).union
      (isCompact_iUnion (lpsOriginalFilledTopology_closedPatch_isCompact N))
end QEC.Coding.TannerLiftedProduct
