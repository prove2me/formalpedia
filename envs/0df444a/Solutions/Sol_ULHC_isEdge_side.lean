-- Prove2me | solution 1 for ULHC.isEdge_side
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:43:51.364189+00:00
-- url     : https://prove2.me/submissions/a0b71fb2-a514-48fc-a9c3-0c55fad3b970

import Definitions.Def_ULHC_L57
import Definitions.Def_ULHC_Dual
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
theorem _root_.solution {V : Finset Pt} {c : Pt} (hc : IsCell V c) (tf : Side) : IsEdge V (sideEdge c tf) := by
  obtain ⟨x, y⟩ := c
  obtain ⟨h1, h2, h3, h4⟩ := hc
  cases tf <;> simp [IsEdge, sideEdge, bot, top, lft, rgt, Edge.q] <;>
    exact ⟨by assumption, by assumption⟩
end ULHC
