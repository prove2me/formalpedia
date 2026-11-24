-- Prove2me | solution 1 for ULHC.D_flip_sink
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:06:17.29658+00:00
-- url     : https://prove2.me/submissions/362c7dff-91e1-4c4d-8b7b-d46f91f692ad

import Definitions.Def_ULHC_Arcs
import Definitions.Def_ULHC_D
import Theorems.Thm_ULHC_D_flip_formula
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
namespace ULHC
theorem _root_.solution {F H : Finset Edge} {c : Pt} (h : Sink F c) (x : Pt) :
    D (flip F c) H x = D F H x - (if x = c then 2 else 0) := by
  have hl := h .l
  have hr := h .r
  simp only [outArc, Bool.not_eq_false'] at hl hr
  have := D_flip_formula F H c x
  rw [hl, hr] at this
  obtain ⟨x1, x2⟩ := x
  obtain ⟨c1, c2⟩ := c
  simp only [Prod.mk.injEq, ite_true, Bool.false_eq_true, ite_false] at this ⊢
  split_ifs at this ⊢ <;> omega
end ULHC
