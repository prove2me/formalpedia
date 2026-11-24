-- Prove2me | solution 1 for ULHC.deg_front2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:47:54.754887+00:00
-- url     : https://prove2.me/submissions/86c56832-59be-4ca8-8a7d-eb4efaaad9cb

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
    deg F (front2 c s) =
      ind F (lat2 c s) + ind F (front c s) + ind F (lat2 (nb c s) s) + ind F (outer2 c s) := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp only [deg, front2, lat2, front, outer2, nb, sideEdge, eR, eL, eU, eD,
    lft, rgt, bot, top] <;> (try simp only [add_sub_cancel_right]) <;> omega
end ULHC
