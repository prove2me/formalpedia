-- Prove2me | solution 2 for PeriodicConstantApprox.translated_axis_cells_cover_uniquely
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:10:26.700888+00:00
-- url     : https://prove2.me/submissions/0206c32d-4c2b-4cea-a70e-f1c9fa13d742

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


theorem solution (L : ℝ) (hL : 0 < L)
    (v : axisCellLattice (d := d) L hL) :
    ∀ x, ∃! g : axisCellLattice (d := d) L hL, g +ᵥ x ∈ v +ᵥ axisAlignedCell (d := d) L := by
  intro x
  obtain ⟨g0, hg0, hu⟩ := PeriodicConstant.axis_cell_translates_cover_uniquely (d := d) L hL x
  refine ⟨g0 + v, ?_, ?_⟩
  · show (g0 + v) +ᵥ x ∈ v +ᵥ axisAlignedCell (d := d) L
    rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_vadd]
    convert hg0 using 2
    abel
  · intro g hg
    change g +ᵥ x ∈ v +ᵥ axisAlignedCell (d := d) L at hg
    rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_vadd] at hg
    have := hu _ hg
    rw [← this]
    abel

