-- Prove2me | solution 1 for PeriodicConstantApprox.ball_subset_translated_cell_of_interior
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:36.514984+00:00
-- url     : https://prove2.me/submissions/c8155d94-4ed7-4b31-b106-5a1cc2004e2e

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_metric_ball_subset_inset_axis_cell

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
theorem _root_.solution {L r : ℝ} (hL : 0 < L)
    {v : axisCellLattice (d := d) L hL} {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ v +ᵥ insetAxisAlignedCell (d := d) L r) :
    ball x r ⊆ v +ᵥ axisAlignedCell (d := d) L := by
  have hx' : (- (v : EuclideanSpace ℝ (Fin d))) +ᵥ x ∈ insetAxisAlignedCell (d := d) L r := by
    simpa [Set.mem_vadd_set_iff_neg_vadd_mem] using! hx
  have hball : ball ((- (v : EuclideanSpace ℝ (Fin d))) +ᵥ x) r ⊆ axisAlignedCell (d := d) L :=
    metric_ball_subset_inset_axis_cell (d := d) (L := L) (r := r) hx'
  have h :=
    translated_ball_subset_translated_region (d := d) (Λ := axisCellLattice (d := d) L hL) (D := axisAlignedCell (d := d) L)
      (g := v) (x := (- (v : EuclideanSpace ℝ (Fin d))) +ᵥ x) (r := r) hball
  simpa [add_vadd, Submodule.vadd_def, vadd_eq_add, add_assoc, add_comm] using! h
end PeriodicConstantApprox
