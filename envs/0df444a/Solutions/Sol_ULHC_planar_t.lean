-- Prove2me | solution 1 for ULHC.planar_t
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:10:58.912884+00:00
-- url     : https://prove2.me/submissions/28e2d41e-ca2f-49d8-8890-308567900a09

import Definitions.Def_ULHC_Iso
import Definitions.Def_ULHC_Strip
import Theorems.Thm_ULHC_not_conn_swap
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_planar_cell
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution (G : Finset Edge) (c : Pt) (h1 : lat1 c .t ∉ G) (h2 : back c .t ∉ G)
    (h3 : Conn G (front1 c .t) (back2 c .t)) (h4 : Conn G (front2 c .t) (back1 c .t))
    (h5 : ¬ Conn G (back1 c .t) (front1 c .t)) : False := by
  obtain ⟨x, y⟩ := c
  simp only [lat1, back, sideEdge, Side.opp, front1, back1, back2, front2] at *
  exact planar_cell G x y h2 h1 h3.symm h4 (not_conn_swap h3 h5)
end ULHC
