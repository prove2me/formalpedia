-- Prove2me | solution 2 for PeriodicConstantApprox.translated_axis_cell_subset_ball
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:07:23.750106+00:00
-- url     : https://prove2.me/submissions/c585c2eb-8823-4fa7-9dbc-a7a82e3e6a8a

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


theorem solution {L : ℝ} (hL : 0 < L) {R C : ℝ}
    (hC : axisAlignedCell (d := d) L ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) C)
    {g : axisCellLattice (d := d) L hL}
    (hg : (g : EuclideanSpace ℝ (Fin d)) ∈ ball 0 (R + C)) :
    g +ᵥ axisAlignedCell (d := d) L ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) (R + (2 * C)) := by
  rintro y ⟨c, hc, rfl⟩
  have h1 := hC hc
  rw [mem_ball, dist_zero_right] at h1 hg ⊢
  show ‖(g : EuclideanSpace ℝ (Fin d)) + c‖ < R + 2 * C
  calc ‖(g : EuclideanSpace ℝ (Fin d)) + c‖ ≤ ‖(g : EuclideanSpace ℝ (Fin d))‖ + ‖c‖ := norm_add_le _ _
    _ < R + 2 * C := by linarith

