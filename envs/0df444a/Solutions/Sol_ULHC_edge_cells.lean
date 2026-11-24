-- Prove2me | solution 1 for ULHC.edge_cells
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:48:54.586313+00:00
-- url     : https://prove2.me/submissions/ff3d3bfa-47cc-4538-9c8c-6ada6ccc6b8d

import Definitions.Def_ULHC_Phase2
import Definitions.Def_ULHC_TheoremA
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
theorem _root_.solution (F : Finset Edge) (e : Edge) :
    ∃ sh sl, sideEdge e.hi sh = e ∧ nb e.hi sh = e.lo ∧ outArc F e.hi sh = !up F e ∧
      sideEdge e.lo sl = e ∧ nb e.lo sl = e.hi ∧ outArc F e.lo sl = up F e := by
  obtain ⟨d, x, y⟩ := e
  cases d
  · refine ⟨.b, .t, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [sideEdge, nb, outArc, bot, top, Edge.lo, Edge.hi]
  · refine ⟨.l, .r, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [sideEdge, nb, outArc, lft, rgt, Edge.lo, Edge.hi]
end ULHC
