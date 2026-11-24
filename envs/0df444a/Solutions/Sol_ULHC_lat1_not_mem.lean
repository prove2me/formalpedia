-- Prove2me | solution 1 for ULHC.lat1_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:19:54.776801+00:00
-- url     : https://prove2.me/submissions/0669eafc-f644-4ad4-ab07-a3ed9dea06c6

import Definitions.Def_ULHC_Strip
import Definitions.Def_ULHC_StripCount
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
theorem _root_.solution {j m : ℕ} (h : j ≠ m) : lat1 (cellJ c s j) s ∉ cellE (cellJ c s m) := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp [cellE, lat1, cellJ, bot, top, lft, rgt] <;> omega
end ULHC
