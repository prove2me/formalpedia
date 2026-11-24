-- Prove2me | solution 1 for ULHC.outArc_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:40:45.965861+00:00
-- url     : https://prove2.me/submissions/d622a8ac-0b1b-47b6-84c7-bd8ce4ffeba2

import Definitions.Def_ULHC_Potential
import Definitions.Def_ULHC_Arcs
import Theorems.Thm_ULHC_par_sub_fst
import Theorems.Thm_ULHC_par_sub_snd
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
namespace ULHC
theorem _root_.solution (F : Finset Edge) (c : Pt) (s : Side) :
    outArc F c s =
      if s.horiz then (par c == decide (sideEdge c s ∈ F))
      else !(par c == decide (sideEdge c s ∈ F)) := by
  obtain ⟨x, y⟩ := c
  cases s
  · have := par_sub_snd (x, y)
    simp only at this
    simp only [outArc, up, inE1, Side.horiz, sideEdge, bot, Edge.lo, this, ite_true]
    cases par (x, y) <;> by_cases hm : (⟨.h, (x, y)⟩ : Edge) ∈ F <;> simp [hm]
  · simp only [outArc, up, inE1, Side.horiz, sideEdge, top, Edge.lo, add_sub_cancel_right,
      ite_true]
    rfl
  · have := par_sub_fst (x, y)
    simp only at this
    simp only [outArc, up, inE1, Side.horiz, sideEdge, lft, Edge.lo, this, ite_false,
      Bool.false_eq_true]
    cases par (x, y) <;> by_cases hm : (⟨.v, (x, y)⟩ : Edge) ∈ F <;> simp [hm]
  · simp only [outArc, up, inE1, Side.horiz, sideEdge, rgt, Edge.lo, add_sub_cancel_right,
      ite_false, Bool.false_eq_true]
    cases par (x, y) <;> by_cases hm : (⟨.v, (x + 1, y)⟩ : Edge) ∈ F <;> simp [hm]
end ULHC
