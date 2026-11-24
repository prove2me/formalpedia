-- Prove2me | solution 1 for ULHC.D_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:07:29.170192+00:00
-- url     : https://prove2.me/submissions/25a7d76d-aeb6-4c09-b393-a2bd293ca2a1

import Definitions.Def_ULHC_Arcs
import Definitions.Def_ULHC_D
import Theorems.Thm_ULHC_wb_not
import Theorems.Thm_ULHC_step_aux
import Theorems.Thm_ULHC_D_jump
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge}
  (hF : IsFactor V d F) (hH : IsFactor V d H)
include hF hH
namespace ULHC
theorem _root_.solution (c : Pt) (s : Side) :
    (if outArc F c s then D F H (nb c s) - D F H c else D F H c - D F H (nb c s)) =
      if (decide (sideEdge c s ∈ F) ^^ decide (sideEdge c s ∈ H)) then 2 else 0 := by
  obtain ⟨x, y⟩ := c
  cases s
  · have j := D_jump hF hH (bot (x, y))
    simp only [bot, Edge.hi_mk, Edge.lo_h] at j
    simp only [outArc, nb, sideEdge, bot]
    apply step_aux; rw [wb_not]; unfold wD at j
    exact (neg_sub _ _).symm.trans (congrArg Neg.neg j)
  · have j := D_jump hF hH (top (x, y))
    simp only [top, Edge.hi_mk, Edge.lo_h, add_sub_cancel_right] at j
    simp only [outArc, nb, sideEdge, top]
    apply step_aux; unfold wD at j; exact j
  · have j := D_jump hF hH (lft (x, y))
    simp only [lft, Edge.hi_mk, Edge.lo_v] at j
    simp only [outArc, nb, sideEdge, lft]
    apply step_aux; rw [wb_not]; unfold wD at j
    exact (neg_sub _ _).symm.trans (congrArg Neg.neg j)
  · have j := D_jump hF hH (rgt (x, y))
    simp only [rgt, Edge.hi_mk, Edge.lo_v, add_sub_cancel_right] at j
    simp only [outArc, nb, sideEdge, rgt]
    apply step_aux; unfold wD at j; exact j
end ULHC
