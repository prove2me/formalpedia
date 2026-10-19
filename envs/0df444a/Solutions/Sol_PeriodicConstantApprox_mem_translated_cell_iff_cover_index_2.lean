-- Prove2me | solution 2 for PeriodicConstantApprox.mem_translated_cell_iff_cover_index
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:21:15.874677+00:00
-- url     : https://prove2.me/submissions/d685079f-5291-46aa-a3d1-46df57c4762f

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


theorem solution (g : axisCellLattice (d := d) L hL)
    (x : EuclideanSpace ℝ (Fin d)) :
    x ∈ g +ᵥ axisAlignedCell (d := d) L ↔ g = -axisCellCoverIndex (d := d) L hL x := by
  have hspec := Classical.choose_spec (PeriodicConstant.axis_cell_translates_cover_uniquely (d := d) L hL x)
  rw [Set.mem_vadd_set_iff_neg_vadd_mem]
  constructor
  · intro h
    have := hspec.2 (-g) h
    unfold axisCellCoverIndex
    rw [← this, neg_neg]
  · intro h
    rw [h, neg_neg]
    exact hspec.1

