-- Prove2me | solution 1 for ULHC.mem_inc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:16:10.461429+00:00
-- url     : https://prove2.me/submissions/e01a4282-404e-4b38-9dc0-652d308c50ee

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
theorem _root_.solution {y : Pt} {e : Edge} : e ∈ inc y ↔ e.p = y ∨ e.q = y := by
  obtain ⟨d, p1, p2⟩ := e
  obtain ⟨y1, y2⟩ := y
  cases d <;> simp [inc, eR, eU, eL, eD, Edge.q] <;> omega
end ULHC
