-- Prove2me | solution 1 for PeriodicConstantApprox.finite_cell_union_subset_enclosing_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:36.514984+00:00
-- url     : https://prove2.me/submissions/336a7dc4-bef6-4156-808b-7d8239591a2c

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_PeriodicConstantApprox_translated_axis_cell_subset_ball

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
    (hC : axisAlignedCell (d := d) L ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) C) :
    let htSet :=
      PeriodicConstantApprox.lattice_points_in_ball_finite (d := d) L hL (R + C)
    let t : Finset (axisCellLattice (d := d) L hL) := htSet.toFinset
    (⋃ g ∈ t, g +ᵥ axisAlignedCell (d := d) L) ⊆
      ball (0 : EuclideanSpace ℝ (Fin d)) (R + (2 * C)) := by
  intro htSet t y hy
  rcases Set.mem_iUnion₂.1 hy with ⟨g, hgT, hy'⟩
  have hgBall :
      (g : EuclideanSpace ℝ (Fin d)) ∈ ball (0 : EuclideanSpace ℝ (Fin d)) (R + C) :=
    htSet.mem_toFinset.1 (by simpa [t] using! hgT)
  exact (translated_axis_cell_subset_ball (d := d) (hL := hL) (R := R) (C := C) hC hgBall) hy'
end PeriodicConstantApprox
