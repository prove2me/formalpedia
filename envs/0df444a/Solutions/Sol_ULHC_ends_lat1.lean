-- Prove2me | solution 1 for ULHC.ends_lat1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:46:26.285355+00:00
-- url     : https://prove2.me/submissions/c8f01b8c-15ea-470a-b0ee-a159430cd0b7

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
theorem _root_.solution : Ends (lat1 c s) (back1 c s) (front1 c s) := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp [Ends, lat1, back1, front1, lft, bot, Edge.q]
end ULHC
