-- Prove2me | solution 1 for ULHC.outer2_side_nb_next
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:27:45.228587+00:00
-- url     : https://prove2.me/submissions/6d9a21aa-9b6d-4324-8bb1-14d4ff4a0bd5

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
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
variable (c : Pt) (s : Side)
namespace ULHC
theorem _root_.solution : outer2 c s = sideEdge (nb (nb c s) (latB s)) s.opp := by
  obtain ⟨x, y⟩ := c; cases s <;> simp [outer2, latB, sideEdge, nb, Side.opp, bot, top, lft, rgt]
end ULHC
