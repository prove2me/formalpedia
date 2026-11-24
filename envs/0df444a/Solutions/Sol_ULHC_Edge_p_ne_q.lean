-- Prove2me | solution 1 for ULHC.Edge.p_ne_q
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:49:20.769909+00:00
-- url     : https://prove2.me/submissions/759a5329-c136-4d92-a5ef-1f060d5f1c17

import Definitions.Def_ULHC_Planar
import Definitions.Def_ULHC_Graph
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
open Finset Classical
namespace ULHC
namespace Edge
theorem _root_.solution (e : Edge) : e.p ≠ e.q := by
  obtain ⟨d, p1, p2⟩ := e
  cases d <;> simp [Edge.q]
end Edge
end ULHC
