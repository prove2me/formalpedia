-- Prove2me | solution 1 for ULHC.outer1_side_nb_next
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:43:01.474569+00:00
-- url     : https://prove2.me/submissions/18ead6a0-3686-4fe0-b64d-c12f431db5f6

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
theorem _root_.solution : outer1 c s = sideEdge (nb (nb c s) (latA s)) s.opp := by
  obtain ⟨x, y⟩ := c; cases s <;> simp [outer1, latA, sideEdge, nb, Side.opp, bot, top, lft, rgt]
end ULHC
