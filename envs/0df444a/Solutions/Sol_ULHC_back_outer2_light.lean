-- Prove2me | solution 1 for ULHC.back_outer2_light
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:16:50.906332+00:00
-- url     : https://prove2.me/submissions/abddd94b-4b78-4a6a-a810-772de059839b

import Definitions.Def_ULHC_Enum
import Definitions.Def_ULHC_L57
import Definitions.Def_ULHC_Created
import Definitions.Def_ULHC_Near
import Theorems.Thm_ULHC_side2_back1
import Theorems.Thm_ULHC_side2_front1
import Theorems.Thm_ULHC_side2_lat1
import Theorems.Thm_ULHC_side2_front
import Theorems.Thm_ULHC_side2_back_ends
import Theorems.Thm_ULHC_side2_front_ends
import Theorems.Thm_ULHC_corners4
import Theorems.Thm_ULHC_ind_of_mem
import Theorems.Thm_ULHC_ind_of_not_mem
import Theorems.Thm_ULHC_front_join
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_DWalk_trans
import Theorems.Thm_ULHC_Ends_conn
import Theorems.Thm_ULHC_Ends_inV
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_PStep_symm
import Theorems.Thm_ULHC_cellJ_zero
import Theorems.Thm_ULHC_deg_front2
import Theorems.Thm_ULHC_ends_back
import Theorems.Thm_ULHC_ends_front
import Theorems.Thm_ULHC_ends_lat2
import Theorems.Thm_ULHC_isCell_of_corners
import Theorems.Thm_ULHC_nb_cellJ


set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} (hF : Deg2 V F) {c : Pt} {s : Side} {n : ℕ}
include hF
variable (hT : NoTypeIII V F)
include hT
namespace ULHC
theorem _root_.solution (hp : StripPat F c s n) (hn : 2 ≤ n) (hc : IsCell V c)
    (hsep : ¬ Conn F (back1 c s) (front1 c s)) : back (nb c (latB s)) s ∉ F := by
  intro hb
  set L := nb c (latB s)
  have hsep2 : ¬ Conn F (back2 c s) (front2 c s) := fun h => hsep
    ((((ends_back c s).conn hp.1).trans h).trans (front_join hF hT hp hn hc).symm)
  have ho : outer2 c s ∈ F := by
    obtain ⟨_, hl, hf⟩ := hp
    have h0 := hl 0 (by omega)
    have h1 := hl 1 (by omega)
    have hf0 := hf 0 (by omega)
    rw [cellJ_zero] at h0 hf0
    have hl0 : lat2 c s ∉ F := fun h => by have := h0.2.1 h; omega
    have hfr : front c s ∉ F := fun h => by have := hf0.1 h; omega
    have hl1 : lat2 (nb c s) s ∈ F := by
      rw [show nb c s = cellJ c s 1 by rw [← nb_cellJ, cellJ_zero]]; exact h1.2.2 rfl
    have hd := hF.2 _ (corners4 hc s).2.2.2
    rw [deg_front2, ind_of_not_mem hl0, ind_of_not_mem hfr, ind_of_mem hl1] at hd
    by_contra ho
    rw [ind_of_not_mem ho] at hd
    omega
  have hfL : front L s ∈ F := by rw [side2_front]; exact ho
  have hV1 := (side2_back_ends c s).inV (hF.1 _ hb)
  have hV2 := (side2_front_ends c s).inV (hF.1 _ ho)
  have hcL : IsCell V L := by
    refine isCell_of_corners L s ?_ hV1.2 ?_ hV2.2
    · rw [side2_back1]; exact hV1.1
    · rw [side2_front1]; exact hV2.1
  have hl1 : lat1 L s ∉ F := by
    rw [side2_lat1]
    obtain ⟨_, hl', _⟩ := hp
    have h0 := hl' 0 (by omega)
    rw [cellJ_zero] at h0
    exact fun h => by have := h0.2.1 h; omega
  have hLL : Conn F (back1 L s) (front1 L s) := by
    by_cases hl : lat2 L s ∈ F
    · exact ((((ends_back L s).conn hb).trans ((ends_lat2 L s).conn hl)).trans
        ((ends_front L s).conn hfL).symm)
    · exact hT L hcL s hb hfL hl1 hl
  rw [side2_back1, side2_front1] at hLL
  exact hsep2 hLL
end ULHC
