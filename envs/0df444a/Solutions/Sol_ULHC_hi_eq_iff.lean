-- Prove2me | solution 1 for ULHC.hi_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:51:13.498792+00:00
-- url     : https://prove2.me/submissions/50d791db-8147-415f-aba1-0c99b5e33b11

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
theorem _root_.solution (e : Edge) (c : Pt) : e.hi = c ↔ (e = bot c ∨ e = lft c) := by
  obtain ⟨d, p⟩ := e
  cases d <;> simp [Edge.hi, bot, lft]
end ULHC
