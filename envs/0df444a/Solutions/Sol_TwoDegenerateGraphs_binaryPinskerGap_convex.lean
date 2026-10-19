-- Prove2me | solution 1 for TwoDegenerateGraphs.binaryPinskerGap_convex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:04.05007+00:00
-- url     : https://prove2.me/submissions/c11ee8cc-ab8d-45db-9b02-9ce9da1e778e

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_binaryPinskerGap_continuous
import Theorems.Thm_TwoDegenerateGraphs_binaryPinskerGap_hasDerivAt
import Theorems.Thm_TwoDegenerateGraphs_binaryPinskerGapDeriv_hasDerivAt
import Theorems.Thm_TwoDegenerateGraphs_binaryPinskerGapDerivTwo_nonneg

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution :
    ConvexOn ℝ (Set.Icc 0 1) binaryPinskerGap := by
  refine convexOn_of_hasDerivWithinAt2_nonneg
    (f' := binaryPinskerGapDeriv)
    (f'' := binaryPinskerGapDerivTwo)
    (convex_Icc (0 : ℝ) 1)
    binaryPinskerGap_continuous.continuousOn ?_ ?_ ?_
  · intro q hq
    have hq' : q ∈ Set.Ioo (0 : ℝ) 1 := by
      simpa only [interior_Icc] using hq
    exact (binaryPinskerGap_hasDerivAt hq'.1.ne' hq'.2.ne).hasDerivWithinAt
  · intro q hq
    have hq' : q ∈ Set.Ioo (0 : ℝ) 1 := by
      simpa only [interior_Icc] using hq
    exact
      (binaryPinskerGapDeriv_hasDerivAt hq'.1.ne' hq'.2.ne).hasDerivWithinAt
  · intro q hq
    have hq' : q ∈ Set.Ioo (0 : ℝ) 1 := by
      simpa only [interior_Icc] using hq
    exact binaryPinskerGapDerivTwo_nonneg hq'.1 hq'.2
end TwoDegenerateGraphs
