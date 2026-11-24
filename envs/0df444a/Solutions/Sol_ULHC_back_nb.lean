-- Prove2me | solution 1 for ULHC.back_nb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:47:35.688399+00:00
-- url     : https://prove2.me/submissions/c3cd8f84-e93a-4868-adc1-72bb5b768c94

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
theorem _root_.solution : back (nb c s) s = front c s := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp [back, front, nb, sideEdge, Side.opp, bot, top, lft, rgt]
end ULHC
