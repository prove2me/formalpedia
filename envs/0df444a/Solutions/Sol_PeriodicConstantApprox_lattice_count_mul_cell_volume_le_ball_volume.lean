-- Prove2me | solution 1 for PeriodicConstantApprox.lattice_count_mul_cell_volume_le_ball_volume
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:36.514984+00:00
-- url     : https://prove2.me/submissions/eb939547-8cc8-4637-bd9f-c6a914b1a1de

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_PeriodicConstant_axis_cell_is_measurable
import Theorems.Thm_PeriodicConstantApprox_finite_cell_union_subset_enclosing_ball

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
theorem _root_.solution {L : ℝ} (hL : 0 < L)
    {R C : ℝ} (hC : axisAlignedCell (d := d) L ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) C) :
    let htSet :=
      PeriodicConstantApprox.lattice_points_in_ball_finite (d := d) L hL (R + C)
    let t : Finset (axisCellLattice (d := d) L hL) := htSet.toFinset
    (t.card : ℝ≥0∞) * volume (axisAlignedCell (d := d) L) ≤
      volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + (2 * C))) := by
  intro htSet t
  have hdisj :
      Set.PairwiseDisjoint (↑t : Set (axisCellLattice (d := d) L hL))
        (fun g : axisCellLattice (d := d) L hL => g +ᵥ axisAlignedCell (d := d) L) := by
    intro g _ h _ hgh
    exact translates_disjoint_of_unique_cover (d := d)
      (Λ := axisCellLattice (d := d) L hL) (D := axisAlignedCell (d := d) L)
      (PeriodicConstant.axis_cell_translates_cover_uniquely (d := d) L hL) hgh
  have hmeas :
      ∀ g ∈ t, MeasurableSet (g +ᵥ axisAlignedCell (d := d) L) := by
    intro g _; simpa using!
      (MeasurableSet.const_vadd (PeriodicConstant.axis_cell_is_measurable (d := d) L hL) g)
  have hvol_union :
      volume (⋃ g ∈ t, g +ᵥ axisAlignedCell (d := d) L) =
        ∑ g ∈ t, volume (g +ᵥ axisAlignedCell (d := d) L) :=
    measure_biUnion_finset (μ := volume) hdisj hmeas
  have hsub :
      (⋃ g ∈ t, g +ᵥ axisAlignedCell (d := d) L) ⊆
        ball (0 : EuclideanSpace ℝ (Fin d)) (R + (2 * C)) :=
    finite_cell_union_subset_enclosing_ball (d := d) (hL := hL) (R := R) (C := C) hC
  have hle := volume.mono hsub
  simp_all
end PeriodicConstantApprox
