-- Prove2me | solution 2 for SpherePacking.upper_packing_density_le_one
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:24:41.841513+00:00
-- url     : https://prove2.me/submissions/1ce272c2-189f-49cd-a9eb-4cc14a52e002

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open MeasureTheory Metric Filter
open Module
open scoped BigOperators ENNReal Pointwise
open SpherePacking


theorem solution {d : ℕ} (S : SpherePacking d) : S.upperPackingDensity ≤ 1 := by
  unfold SpherePacking.upperPackingDensity
  refine Filter.limsup_le_of_le (h := Filter.Eventually.of_forall fun R => ?_)
  unfold SpherePacking.densityInsideRadius
  exact ENNReal.div_le_of_le_mul (by rw [one_mul]; exact measure_mono Set.inter_subset_right)

