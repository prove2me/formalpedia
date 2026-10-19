-- Prove2me | solution 2 for PeriodicConstantApprox.mem_negated_cover_index_cell
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:07:22.254144+00:00
-- url     : https://prove2.me/submissions/129f787e-affb-4411-93fd-d32e0729a860

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
open Metric
variable (L : ℝ) (hL : 0 < L)


theorem solution (x : EuclideanSpace ℝ (Fin d)) :
    x ∈ (-axisCellCoverIndex (d := d) L hL x) +ᵥ axisAlignedCell (d := d) L := by
  rw [Set.mem_vadd_set_iff_neg_vadd_mem, neg_neg]
  exact (Classical.choose_spec
    (PeriodicConstant.axis_cell_translates_cover_uniquely (d := d) L hL x)).1

