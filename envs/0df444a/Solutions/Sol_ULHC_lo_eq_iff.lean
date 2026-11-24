-- Prove2me | solution 1 for ULHC.lo_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:51:20.642576+00:00
-- url     : https://prove2.me/submissions/86f74d48-0778-4e20-85e2-24e1ef36c9d4

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
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
theorem _root_.solution (e : Edge) (c : Pt) : e.lo = c ↔ (e = top c ∨ e = rgt c) := by
  obtain ⟨d, p1, p2⟩ := e
  obtain ⟨x, y⟩ := c
  cases d <;> simp [Edge.lo, top, rgt] <;> omega
end ULHC
