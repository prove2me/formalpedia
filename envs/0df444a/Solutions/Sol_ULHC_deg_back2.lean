-- Prove2me | solution 1 for ULHC.deg_back2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:02:50.397798+00:00
-- url     : https://prove2.me/submissions/b59af0c9-91c5-4333-bd72-ff89ec09b1c9

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
    deg F (back2 c s) =
      ind F (lat2 c s) + ind F (back c s) + ind F (lat2 (nb c s.opp) s) +
        ind F (back (nb c (latB s)) s) := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp only [deg, back2, lat2, back, nb, sideEdge, Side.opp, latB, eR, eL, eU, eD,
    lft, rgt, bot, top] <;> (try simp only [add_sub_cancel_right]) <;> omega
end ULHC
