-- Prove2me | solution 1 for PeriodicConstantApprox.negated_cover_index_mem_enlarged_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:36.514984+00:00
-- url     : https://prove2.me/submissions/7d747da4-89e3-41bb-b931-073602bc6c0d

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
theorem _root_.solution {C R : ℝ}
    (hC : axisAlignedCell (d := d) L ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) C)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ ball 0 R) :
    ((-axisCellCoverIndex (d := d) L hL x : axisCellLattice (d := d) L hL) :
        EuclideanSpace ℝ (Fin d)) ∈ ball 0 (R + C) := by
  have hx0 : ‖x‖ < R := by simpa [mem_ball_zero_iff] using! hx
  have hxgC : ‖(axisCellCoverIndex (d := d) L hL x : EuclideanSpace ℝ (Fin d)) + x‖ < C := by
    have hmem :
        (axisCellCoverIndex (d := d) L hL x : EuclideanSpace ℝ (Fin d)) + x ∈ axisAlignedCell (d := d) L := by
      simpa [Submodule.vadd_def, vadd_eq_add] using! axis_cell_cover_index_mem (d := d) L hL x
    simpa [mem_ball_zero_iff] using! (hC hmem)
  have htri :
      ‖(axisCellCoverIndex (d := d) L hL x : EuclideanSpace ℝ (Fin d))‖ ≤
        ‖(axisCellCoverIndex (d := d) L hL x : EuclideanSpace ℝ (Fin d)) + x‖ + ‖x‖ := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using!
      (norm_sub_le (a := (axisCellCoverIndex (d := d) L hL x : EuclideanSpace ℝ (Fin d)) + x) (b := x))
  have :
      ‖(- (axisCellCoverIndex (d := d) L hL x : EuclideanSpace ℝ (Fin d)))‖ < R + C := by
    have : ‖(axisCellCoverIndex (d := d) L hL x : EuclideanSpace ℝ (Fin d))‖ < C + R := by
      refine lt_of_le_of_lt htri ?_
      simpa [add_comm, add_left_comm, add_assoc] using! add_lt_add hxgC hx0
    simpa [norm_neg, add_comm, add_left_comm, add_assoc] using! this
  simpa [mem_ball_zero_iff] using! this
end PeriodicConstantApprox
