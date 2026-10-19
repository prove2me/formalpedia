-- Prove2me | solution 2 for PeriodicConstantApprox.axis_cell_cover_index_unique
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:07:20.929146+00:00
-- url     : https://prove2.me/submissions/177b7d34-ed03-4df8-bc51-b9f4ff46a441

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


theorem solution (x : EuclideanSpace ℝ (Fin d)) (g : axisCellLattice (d := d) L hL)
    (hg : g +ᵥ x ∈ axisAlignedCell (d := d) L) :
    g = axisCellCoverIndex (d := d) L hL x := by
  exact (Classical.choose_spec
    (PeriodicConstant.axis_cell_translates_cover_uniquely (d := d) L hL x)).2 g hg

