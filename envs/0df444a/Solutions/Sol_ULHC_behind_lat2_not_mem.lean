-- Prove2me | solution 1 for ULHC.behind_lat2_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:14:44.719648+00:00
-- url     : https://prove2.me/submissions/5df72bf4-d0f7-4198-9b46-1577b789c4db

import Definitions.Def_ULHC_Reverse
import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
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
namespace ULHC
theorem _root_.solution (c : Pt) (s : Side) (j : ℕ) :
    lat2 (nb c s.opp) s ∉ cellE (cellJ c s j) := by
  obtain ⟨x, y⟩ := c; cases s <;> simp [cellE, lat2, nb, cellJ, Side.opp, bot, top, lft, rgt] <;> omega
end ULHC
