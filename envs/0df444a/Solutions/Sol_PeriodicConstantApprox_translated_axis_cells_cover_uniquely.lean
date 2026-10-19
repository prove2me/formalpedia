-- Prove2me | solution 1 for PeriodicConstantApprox.translated_axis_cells_cover_uniquely
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:36.514984+00:00
-- url     : https://prove2.me/submissions/b7218fd3-72ee-4eef-bb6f-043d4e38e052

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
namespace PeriodicConstantApprox
theorem _root_.solution (L : ℝ) (hL : 0 < L)
    (v : axisCellLattice (d := d) L hL) :
    ∀ x, ∃! g : axisCellLattice (d := d) L hL, g +ᵥ x ∈ v +ᵥ axisAlignedCell (d := d) L := by
  intro x
  have hvadd (a : axisCellLattice (d := d) L hL) :
      a +ᵥ x ∈ v +ᵥ axisAlignedCell (d := d) L ↔ (a - v) +ᵥ x ∈ axisAlignedCell (d := d) L := by
    simp [Set.mem_vadd_set_iff_neg_vadd_mem, Submodule.vadd_def, vadd_eq_add, sub_eq_add_neg,
      add_assoc, add_comm]
  obtain ⟨g, hg, hguniq⟩ := PeriodicConstant.axis_cell_translates_cover_uniquely (d := d) L hL x
  refine ⟨g + v, (hvadd (a := g + v)).2 (by simpa using! hg), ?_⟩
  intro a ha
  have ha' : (a - v) +ᵥ x ∈ axisAlignedCell (d := d) L := (hvadd a).1 ha
  have : a - v = g := hguniq _ ha'
  exact (sub_eq_iff_eq_add).1 this
end PeriodicConstantApprox
