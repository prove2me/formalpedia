-- Prove2me | solution 1 for ULHC.allConn_side
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:54:38.057807+00:00
-- url     : https://prove2.me/submissions/79d69a5f-ef23-467a-bbf0-814e8b505f4e

import Definitions.Def_ULHC_Reroute
import Definitions.Def_ULHC_Created
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_DWalk_trans
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_PStep_symm
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution {F : Finset Edge} {d : Pt} (h : AllConn F d) (tf : Side) :
    Conn F (sideEdge d tf).p (sideEdge d tf).q := by
  obtain ⟨x, y⟩ := d
  obtain ⟨h1, h2, h3⟩ := h
  cases tf <;> simp only [sideEdge, bot, top, lft, rgt, Edge.q]
  · exact h1
  · exact h2.symm.trans h3
  · exact h2
  · exact h1.symm.trans h3
end ULHC
