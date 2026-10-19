-- Prove2me | solution 1 for PeriodicConstantApprox.axis_cell_subset_enclosing_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:36.514984+00:00
-- url     : https://prove2.me/submissions/b70ec481-e657-4e01-a668-eeb6bffddc02

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_PeriodicConstant_axis_cell_is_bounded

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module
open scoped Pointwise
open scoped Pointwise
open MeasureTheory Metric
open PeriodicConstantApprox
variable {d : ℕ}
namespace PeriodicConstantApprox
theorem _root_.solution (L : ℝ) (hL : 0 < L) :
    ∃ C : ℝ, axisAlignedCell (d := d) L ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) C := by
  simpa using! (PeriodicConstant.axis_cell_is_bounded (d := d) L hL).subset_ball 0
end PeriodicConstantApprox
