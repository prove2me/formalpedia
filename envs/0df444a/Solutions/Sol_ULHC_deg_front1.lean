-- Prove2me | solution 1 for ULHC.deg_front1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:47:28.913294+00:00
-- url     : https://prove2.me/submissions/8e543c7b-e3e6-4b43-8f21-b52ff6cce937

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
theorem _root_.solution (F : Finset Edge) :
    deg F (front1 c s) =
      ind F (lat1 c s) + ind F (front c s) + ind F (lat1 (nb c s) s) + ind F (outer1 c s) := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp only [deg, front1, lat1, front, outer1, nb, sideEdge, eR, eL, eU, eD,
    lft, rgt, bot, top] <;> (try simp only [add_sub_cancel_right]) <;> omega
end ULHC
