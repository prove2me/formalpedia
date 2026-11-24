-- Prove2me | solution 1 for ULHC.outer1_side_nb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:42:42.940832+00:00
-- url     : https://prove2.me/submissions/88f0aa3b-4a8d-4933-bd30-d658839db82b

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
theorem _root_.solution : outer1 c s = sideEdge (nb c (latA s)) s := by
  obtain ⟨x, y⟩ := c; cases s <;> simp [outer1, latA, sideEdge, nb, bot, top, lft, rgt]
end ULHC
