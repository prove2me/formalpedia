-- Prove2me | solution 1 for ULHC.flowL_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:15:59.238434+00:00
-- url     : https://prove2.me/submissions/2b5df3d6-655a-4ad6-a6f9-107787a7fd04

import Definitions.Def_ULHC_Conn
import Definitions.Def_ULHC_Planar
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
theorem _root_.solution (u : Pt) (l₁ l₂ : List Pt) (e : Edge) :
    flowL u (l₁ ++ l₂) e = flowL u l₁ e + flowL ((u :: l₁).getLast (by simp)) l₂ e := by
  induction l₁ generalizing u with
  | nil => simp [flowL]
  | cons v l ih =>
    simp only [List.cons_append, flowL, ih v, List.getLast_cons_cons]
    ring
end ULHC
