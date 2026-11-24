-- Prove2me | solution 1 for ULHC.deg_back1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:02:39.764073+00:00
-- url     : https://prove2.me/submissions/dfd38454-7fe0-404a-89ea-0f8ad04a4d37

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
variable (c : Pt) (s : Side)
namespace ULHC
theorem _root_.solution (F : Finset Edge) :
    deg F (back1 c s) =
      ind F (lat1 c s) + ind F (back c s) + ind F (lat1 (nb c s.opp) s) +
        ind F (back (nb c (latA s)) s) := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp only [deg, back1, lat1, back, nb, sideEdge, Side.opp, latA, eR, eL, eU, eD,
    lft, rgt, bot, top] <;> (try simp only [add_sub_cancel_right]) <;> omega
end ULHC
