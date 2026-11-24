-- Prove2me | solution 1 for ULHC.side_lat1_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:43:08.651552+00:00
-- url     : https://prove2.me/submissions/0cffd16b-0484-46bb-9db8-46d31382086c

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
theorem _root_.solution (j m : ℕ) : lat1 (nb (cellJ c s j) (latA s)) s ∉ cellE (cellJ c s m) := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp [cellE, lat1, latA, nb, cellJ, bot, top, lft, rgt] <;> omega
end ULHC
