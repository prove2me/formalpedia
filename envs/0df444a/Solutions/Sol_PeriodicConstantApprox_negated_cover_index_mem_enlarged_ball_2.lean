-- Prove2me | solution 2 for PeriodicConstantApprox.negated_cover_index_mem_enlarged_ball
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:33:47.738886+00:00
-- url     : https://prove2.me/submissions/7209e534-c3d2-4b32-832b-378a3fbad47c

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


theorem solution {C R : ℝ}
    (hC : axisAlignedCell (d := d) L ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) C)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ ball 0 R) :
    ((-axisCellCoverIndex (d := d) L hL x : axisCellLattice (d := d) L hL) :
        EuclideanSpace ℝ (Fin d)) ∈ ball 0 (R + C) := by
  have h := (Classical.choose_spec (PeriodicConstant.axis_cell_translates_cover_uniquely (d := d) L hL x)).1
  have hm := hC h
  change (((axisCellCoverIndex (d := d) L hL x : axisCellLattice (d := d) L hL) :
      EuclideanSpace ℝ (Fin d)) + x) ∈ ball 0 C at hm
  rw [mem_ball_zero_iff] at hm hx ⊢
  rw [Submodule.coe_neg, norm_neg]
  set g : EuclideanSpace ℝ (Fin d) := ((axisCellCoverIndex (d := d) L hL x : axisCellLattice (d := d) L hL) :
      EuclideanSpace ℝ (Fin d))
  have : ‖g‖ ≤ ‖g + x‖ + ‖x‖ := by
    calc ‖g‖ = ‖(g + x) - x‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖g + x‖ + ‖x‖ := norm_sub_le _ _
  linarith

