-- Prove2me | solution 2 for PeriodicConstantApprox.axis_cell_subset_enclosing_ball
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:03:08.358111+00:00
-- url     : https://prove2.me/submissions/fbff4075-fb15-4dc9-bdb9-9b175f325356

import Mathlib
import Definitions.Def_SpherePacking
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


theorem solution (L : ℝ) (hL : 0 < L) :
    ∃ C : ℝ, axisAlignedCell (d := d) L ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) C := by
  have hb : IsBounded (axisAlignedCell (d := d) L) := by
    refine (isBounded_iff_forall_norm_le).2 ⟨Real.sqrt (∑ _i : Fin d, L ^ 2), fun x hx => ?_⟩
    simp only [axisAlignedCell, Set.mem_setOf_eq, Set.mem_Ico] at hx
    rw [EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum
    intro i _
    rw [Real.norm_eq_abs, sq_abs]
    nlinarith [(hx i).1, (hx i).2]
  exact hb.subset_ball 0

