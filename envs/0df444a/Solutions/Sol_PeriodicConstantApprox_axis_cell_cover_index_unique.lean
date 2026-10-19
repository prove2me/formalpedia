-- Prove2me | solution 1 for PeriodicConstantApprox.axis_cell_cover_index_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:36.514984+00:00
-- url     : https://prove2.me/submissions/6b83f7df-64a7-4349-90a0-3e57da16f49b

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
namespace PeriodicConstantApprox
theorem _root_.solution (x : EuclideanSpace ℝ (Fin d)) (g : axisCellLattice (d := d) L hL)
    (hg : g +ᵥ x ∈ axisAlignedCell (d := d) L) :
    g = axisCellCoverIndex (d := d) L hL x :=
  (Classical.choose_spec (PeriodicConstant.axis_cell_translates_cover_uniquely (d := d) L hL x)).2 g hg
end PeriodicConstantApprox
