-- Prove2me | solution 1 for PeriodicConstantApprox.mem_translated_cell_iff_cover_index
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:36.514984+00:00
-- url     : https://prove2.me/submissions/cc813249-2aca-4071-980a-1ff642a13e2b

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_PeriodicConstantApprox_axis_cell_cover_index_unique
import Theorems.Thm_PeriodicConstantApprox_mem_negated_cover_index_cell

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module
open scoped Pointwise Topology
variable {d : ℕ}
open PeriodicConstantApprox
open Metric
variable (L : ℝ) (hL : 0 < L)
namespace PeriodicConstantApprox
theorem _root_.solution (g : axisCellLattice (d := d) L hL)
    (x : EuclideanSpace ℝ (Fin d)) :
    x ∈ g +ᵥ axisAlignedCell (d := d) L ↔ g = -axisCellCoverIndex (d := d) L hL x := by
  constructor
  · intro hx
    have : (-g : axisCellLattice (d := d) L hL) = axisCellCoverIndex (d := d) L hL x :=
      axis_cell_cover_index_unique (d := d) L hL x (-g)
        (by simpa [Set.mem_vadd_set_iff_neg_vadd_mem] using! hx)
    simpa using! congrArg (fun t : axisCellLattice (d := d) L hL => -t) this
  · rintro rfl; exact mem_negated_cover_index_cell (d := d) L hL x
end PeriodicConstantApprox
