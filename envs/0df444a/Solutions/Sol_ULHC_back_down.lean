-- Prove2me | solution 1 for ULHC.back_down
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:14:00.821316+00:00
-- url     : https://prove2.me/submissions/deaf55aa-b36d-4bd5-b200-0dedec7770b6

import Definitions.Def_ULHC_Enum
import Definitions.Def_ULHC_L57
import Definitions.Def_ULHC_Created
import Definitions.Def_ULHC_Near
import Theorems.Thm_ULHC_deg_back1
import Theorems.Thm_ULHC_corners4
import Theorems.Thm_ULHC_ind_of_mem
import Theorems.Thm_ULHC_ind_of_not_mem
import Theorems.Thm_ULHC_back_outer_light
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_cellJ_zero


set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} (hF : Deg2 V F) {c : Pt} {s : Side} {n : ℕ}
include hF
variable (hT : NoTypeIII V F)
include hT
namespace ULHC
theorem _root_.solution (hp : StripPat F c s n) (hn : 2 ≤ n) (hc : IsCell V c)
    (hsep : ¬ Conn F (back1 c s) (front1 c s)) : lat1 (nb c s.opp) s ∈ F := by
  have hbo := back_outer_light hF hT hp hn hc hsep
  obtain ⟨hbk, hl, _⟩ := hp
  have h0 := hl 0 (by omega)
  rw [cellJ_zero] at h0
  have hl0 : lat1 c s ∉ F := fun h => by have := h0.1.1 h; omega
  have hd := hF.2 _ (corners4 hc s).1
  rw [deg_back1, ind_of_not_mem hl0, ind_of_mem hbk, ind_of_not_mem hbo] at hd
  by_contra hx
  rw [ind_of_not_mem hx] at hd
  omega
end ULHC
