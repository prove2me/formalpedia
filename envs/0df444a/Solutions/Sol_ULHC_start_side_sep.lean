-- Prove2me | solution 1 for ULHC.start_side_sep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:14:38.088056+00:00
-- url     : https://prove2.me/submissions/50d04265-4d0b-47e8-82e8-6b34a646b821

import Definitions.Def_ULHC_Enum
import Definitions.Def_ULHC_L57
import Definitions.Def_ULHC_Created
import Definitions.Def_ULHC_Near
import Theorems.Thm_ULHC_side_back_ends
import Theorems.Thm_ULHC_side_front_ends
import Theorems.Thm_ULHC_corners4
import Theorems.Thm_ULHC_outer1_start
import Theorems.Thm_ULHC_back_outer_light
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_DWalk_trans
import Theorems.Thm_ULHC_Ends_conn
import Theorems.Thm_ULHC_Ends_conn_iff
import Theorems.Thm_ULHC_Ends_inV
import Theorems.Thm_ULHC_Ends_isEdge
import Theorems.Thm_ULHC_GridIso_conn_iff
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_PStep_symm
import Theorems.Thm_ULHC_cellJ_zero
import Theorems.Thm_ULHC_conn_mem
import Theorems.Thm_ULHC_inter_dark_lat
import Theorems.Thm_ULHC_isCell_of_corners
import Theorems.Thm_ULHC_lat1_eq
import Theorems.Thm_ULHC_lat2_eq
import Theorems.Thm_ULHC_latA_opp
import Theorems.Thm_ULHC_latB_opp
import Theorems.Thm_ULHC_side_back2
import Theorems.Thm_ULHC_side_front2
import Theorems.Thm_ULHC_side_lat2


set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} (hF : Deg2 V F) {c : Pt} {s : Side} {n : ℕ}
include hF
variable (hT : NoTypeIII V F)
include hT
namespace ULHC
theorem _root_.solution (hp : StripPat F c s n) (hn : 2 ≤ n) (hc : IsCell V c)
    (hsep : ¬ Conn F (back1 c s) (front1 c s)) (hfar : lat1 (nb c (latA s)) s ∉ F) :
    ¬ Conn F (back1 (nb c (latA s)) s) (front1 (nb c (latA s)) s) := by
  intro h
  set L := nb c (latA s)
  have ho := outer1_start hF hp hn hc
  have hbo := back_outer_light hF hT hp hn hc hsep
  have hV2 := (side_front_ends c s).inV (hF.1 _ ho)
  have hb1 : back1 L s ∈ V := conn_mem hF.1 hV2.1 h.symm
  have hcL : IsCell V L := by
    refine isCell_of_corners L s hb1 ?_ hV2.1 ?_
    · rw [side_back2]; exact (corners4 hc s).1
    · rw [side_front2]; exact hV2.2
  have hbe := side_back_ends c s
  have hI : Inter V F (sideEdge L s.opp) := by
    refine ⟨hbe.isEdge hb1 (corners4 hc s).1, hbo, ?_⟩
    rw [show sideEdge L s.opp = back L s from rfl, hbe.conn_iff]
    intro hx
    exact hsep ((hx.symm.trans h).trans ((side_front_ends c s).conn ho))
  rcases inter_dark_lat hF hT hcL s.opp hI with hx | hx
  · rw [latA_opp, ← lat1_eq] at hx; exact hfar hx
  · rw [latB_opp, ← lat2_eq, side_lat2] at hx
    obtain ⟨_, hl, _⟩ := hp
    have h0 := hl 0 (by omega)
    rw [cellJ_zero] at h0
    have := h0.1.1 hx; omega
end ULHC
