-- Prove2me | solution 1 for ULHC.front_join
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:14:34.876024+00:00
-- url     : https://prove2.me/submissions/dc9a05e3-d96c-42d5-bdba-38267d52a9fc

import Definitions.Def_ULHC_Enum
import Definitions.Def_ULHC_L57
import Definitions.Def_ULHC_Created
import Definitions.Def_ULHC_Near
import Theorems.Thm_ULHC_corners4
import Theorems.Thm_ULHC_Ends_conn_iff
import Theorems.Thm_ULHC_Ends_isEdge
import Theorems.Thm_ULHC_GridIso_conn_iff
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_cellJ_zero
import Theorems.Thm_ULHC_ends_front
import Theorems.Thm_ULHC_inter_dark_lat
import Theorems.Thm_ULHC_lat1_eq
import Theorems.Thm_ULHC_lat2_eq


set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} (hF : Deg2 V F) {c : Pt} {s : Side} {n : ℕ}
include hF
variable (hT : NoTypeIII V F)
include hT
namespace ULHC
theorem _root_.solution (hp : StripPat F c s n) (hn : 2 ≤ n) (hc : IsCell V c) :
    Conn F (front1 c s) (front2 c s) := by
  obtain ⟨_, hl, hf⟩ := hp
  have h0 := hl 0 (by omega)
  have hf0 := hf 0 (by omega)
  rw [cellJ_zero] at h0 hf0
  have hl1 : lat1 c s ∉ F := fun h => by have := h0.1.1 h; omega
  have hl2 : lat2 c s ∉ F := fun h => by have := h0.2.1 h; omega
  have hfr : front c s ∉ F := fun h => by have := hf0.1 h; omega
  have he := ends_front c s
  by_contra hn'
  have hI : Inter V F (sideEdge c s) := by
    have hm := corners4 hc s
    refine ⟨he.isEdge hm.2.2.1 hm.2.2.2, hfr, ?_⟩
    rw [show sideEdge c s = front c s from rfl, he.conn_iff]; exact hn'
  rcases inter_dark_lat hF hT hc s hI with h | h
  · rw [← lat1_eq] at h; exact hl1 h
  · rw [← lat2_eq] at h; exact hl2 h
end ULHC
