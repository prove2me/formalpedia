-- Prove2me | solution 1 for ULHC.outer2_side_nb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:42:56.49879+00:00
-- url     : https://prove2.me/submissions/5e1454c4-4f6f-4890-9eb9-63f590a83c91

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
theorem _root_.solution : outer2 c s = sideEdge (nb c (latB s)) s := by
  obtain ⟨x, y⟩ := c; cases s <;> simp [outer2, latB, sideEdge, nb, bot, top, lft, rgt]
end ULHC
