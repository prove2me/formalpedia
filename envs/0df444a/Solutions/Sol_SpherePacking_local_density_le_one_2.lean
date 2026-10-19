-- Prove2me | solution 2 for SpherePacking.local_density_le_one
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:17:26.450045+00:00
-- url     : https://prove2.me/submissions/a2a1efb4-13d3-4fd1-86dc-3560ab9c55dc

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


theorem solution {d : ℕ} (S : SpherePacking d) (R : ℝ) :
    S.densityInsideRadius R ≤ 1 := by
  unfold SpherePacking.densityInsideRadius
  exact ENNReal.div_le_of_le_mul (by rw [one_mul]; exact measure_mono Set.inter_subset_right)

