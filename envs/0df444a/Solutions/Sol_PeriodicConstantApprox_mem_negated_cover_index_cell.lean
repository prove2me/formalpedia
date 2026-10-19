-- Prove2me | solution 1 for PeriodicConstantApprox.mem_negated_cover_index_cell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:36.514984+00:00
-- url     : https://prove2.me/submissions/156d2954-9c86-4512-94ed-6853acffcb97

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_PeriodicConstantApprox_axis_cell_cover_index_mem

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
theorem _root_.solution (x : EuclideanSpace ℝ (Fin d)) :
    x ∈ (-axisCellCoverIndex (d := d) L hL x) +ᵥ axisAlignedCell (d := d) L := by
  simpa [Set.mem_vadd_set_iff_neg_vadd_mem] using! axis_cell_cover_index_mem (d := d) L hL x
end PeriodicConstantApprox
