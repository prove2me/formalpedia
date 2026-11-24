-- Prove2me | solution 1 for ULHC.ends_back
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:46:19.537572+00:00
-- url     : https://prove2.me/submissions/84720760-11e3-4bdc-acb0-1db12d1d25c7

import Definitions.Def_ULHC_Iso
import Definitions.Def_ULHC_Strip
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
variable (c : Pt) (s : Side)
namespace ULHC
theorem _root_.solution : Ends (back c s) (back1 c s) (back2 c s) := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp [Ends, back, back1, back2, sideEdge, Side.opp, bot, top, lft, rgt, Edge.q]
end ULHC
