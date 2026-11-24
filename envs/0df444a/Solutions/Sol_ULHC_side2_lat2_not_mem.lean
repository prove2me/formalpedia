-- Prove2me | solution 1 for ULHC.side2_lat2_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:52:47.164797+00:00
-- url     : https://prove2.me/submissions/4b61f7b6-e1b0-4115-b2dc-47edd2c94e51

import Definitions.Def_ULHC_Enum
import Definitions.Def_ULHC_L57
import Definitions.Def_ULHC_Created
import Definitions.Def_ULHC_Near
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
theorem _root_.solution (c : Pt) (s : Side) (j m : ℕ) :
    lat2 (nb (cellJ c s j) (latB s)) s ∉ cellE (cellJ c s m) := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp [cellE, lat2, latB, nb, cellJ, bot, top, lft, rgt] <;> omega
end ULHC
