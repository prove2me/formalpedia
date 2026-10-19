-- Prove2me | solution 2 for PeriodicConstantApprox.finite_cell_union_subset_enclosing_ball
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:23:51.464193+00:00
-- url     : https://prove2.me/submissions/80a0be66-daa0-460e-9cf0-f64262bde457

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
    (hC : axisAlignedCell (d := d) L ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) C) :
    let htSet :=
      PeriodicConstantApprox.lattice_points_in_ball_finite (d := d) L hL (R + C)
    let t : Finset (axisCellLattice (d := d) L hL) := htSet.toFinset
    (⋃ g ∈ t, g +ᵥ axisAlignedCell (d := d) L) ⊆
      ball (0 : EuclideanSpace ℝ (Fin d)) (R + (2 * C)) := by
  intro htSet t x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨g, hg, hxg⟩ := hx
  have hg' : (g : EuclideanSpace ℝ (Fin d)) ∈ ball (0 : EuclideanSpace ℝ (Fin d)) (R + C) := by
    simpa [t] using hg
  obtain ⟨y, hy, rfl⟩ := Set.mem_vadd_set.mp hxg
  have hy' := hC hy
  rw [mem_ball_zero_iff] at hg' hy' ⊢
  have he : g +ᵥ y = (g : EuclideanSpace ℝ (Fin d)) + y := rfl
  rw [he]
  linarith [norm_add_le (g : EuclideanSpace ℝ (Fin d)) y]

