-- Prove2me | solution 2 for PeriodicConstant.axis_cell_is_bounded
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:02:54.260988+00:00
-- url     : https://prove2.me/submissions/e70a6e9f-7585-484c-8def-57f132c16e3f

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module
open scoped Pointwise
open PeriodicConstant
variable {d : ℕ}


theorem solution (L : ℝ) (hL : 0 < L) : IsBounded (axisAlignedCell (d := d) L) := by
  refine (isBounded_iff_forall_norm_le).2 ⟨Real.sqrt (∑ _i : Fin d, L ^ 2), fun x hx => ?_⟩
  simp only [axisAlignedCell, Set.mem_setOf_eq, Set.mem_Ico] at hx
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  rw [Real.norm_eq_abs, sq_abs]
  nlinarith [(hx i).1, (hx i).2]

