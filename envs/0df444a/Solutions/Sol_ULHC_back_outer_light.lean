-- Prove2me | solution 1 for ULHC.back_outer_light
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:09:27.238865+00:00
-- url     : https://prove2.me/submissions/76939385-08d7-4f5c-a41e-e3c1d9a12c70

import Definitions.Def_ULHC_Enum
import Definitions.Def_ULHC_L57
import Definitions.Def_ULHC_Created
import Definitions.Def_ULHC_Near
import Theorems.Thm_ULHC_side_back_ends
import Theorems.Thm_ULHC_side_front_ends
import Theorems.Thm_ULHC_outer1_start
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_DWalk_trans
import Theorems.Thm_ULHC_Ends_conn
import Theorems.Thm_ULHC_Ends_inV
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_PStep_symm
import Theorems.Thm_ULHC_cellJ_zero
import Theorems.Thm_ULHC_ends_lat1
import Theorems.Thm_ULHC_isCell_of_corners
import Theorems.Thm_ULHC_side_back2
import Theorems.Thm_ULHC_side_front
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
    (hsep : ¬ Conn F (back1 c s) (front1 c s)) : back (nb c (latA s)) s ∉ F := by
  intro hb
  set L := nb c (latA s)
  have ho := outer1_start hF hp hn hc
  have hfL : front L s ∈ F := by rw [side_front]; exact ho
  have hV1 := (side_back_ends c s).inV (hF.1 _ hb)
  have hV2 := (side_front_ends c s).inV (hF.1 _ ho)
  have hcL : IsCell V L := by
    refine isCell_of_corners L s hV1.1 ?_ hV2.1 ?_
    · rw [side_back2]; exact hV1.2
    · rw [side_front2]; exact hV2.2
  have hLL : Conn F (back1 L s) (front1 L s) := by
    by_cases hl : lat1 L s ∈ F
    · exact (ends_lat1 L s).conn hl
    · have hl2 : lat2 L s ∉ F := by
        rw [side_lat2]
        obtain ⟨_, hl', _⟩ := hp
        have h0 := hl' 0 (by omega)
        rw [cellJ_zero] at h0
        exact fun h => by have := h0.1.1 h; omega
      exact hT L hcL s hb hfL hl hl2
  exact hsep ((((side_back_ends c s).conn hb).symm.trans hLL).trans
    ((side_front_ends c s).conn ho))
end ULHC
