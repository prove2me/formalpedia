-- Prove2me | solution 1 for PeriodicConstantApprox.translated_axis_cell_subset_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:36.514984+00:00
-- url     : https://prove2.me/submissions/583026f7-c701-46eb-8c7a-caccdd082ac6

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module
open scoped Pointwise Topology
variable {d : ℕ}
open PeriodicConstantApprox
open scoped BigOperators
namespace PeriodicConstantApprox
theorem _root_.solution {L : ℝ} (hL : 0 < L) {R C : ℝ}
    (hC : axisAlignedCell (d := d) L ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) C)
    {g : axisCellLattice (d := d) L hL}
    (hg : (g : EuclideanSpace ℝ (Fin d)) ∈ ball 0 (R + C)) :
    g +ᵥ axisAlignedCell (d := d) L ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) (R + (2 * C)) := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  have hx' : ‖x‖ < C := by
    simpa [mem_ball_zero_iff] using! hC hx
  have hg' : ‖(g : EuclideanSpace ℝ (Fin d))‖ < R + C := by
    simpa [mem_ball_zero_iff] using! hg
  have : ‖(g : EuclideanSpace ℝ (Fin d)) + x‖ < R + (2 * C) := by
    refine (lt_of_le_of_lt (norm_add_le _ _) ?_)
    simpa [two_mul, add_assoc, add_left_comm, add_comm] using! add_lt_add hg' hx'
  simpa [Submodule.vadd_def, vadd_eq_add, mem_ball_zero_iff] using! this
end PeriodicConstantApprox
