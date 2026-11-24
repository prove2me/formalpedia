-- Prove2me | solution 1 for ULHC.start_beyond
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:11:39.283669+00:00
-- url     : https://prove2.me/submissions/8a3a7dda-8679-4893-bb8b-00058ce2814d

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Definitions.Def_ULHC_NearCA
import Theorems.Thm_ULHC_start_frame
import Theorems.Thm_ULHC_perp_x
import Theorems.Thm_ULHC_u_across
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_back_nb
import Theorems.Thm_ULHC_beside_end1
import Theorems.Thm_ULHC_beside_end2
import Theorems.Thm_ULHC_corners4
import Theorems.Thm_ULHC_deg_front1
import Theorems.Thm_ULHC_deg_front2
import Theorems.Thm_ULHC_end_side_far1
import Theorems.Thm_ULHC_end_side_far2
import Theorems.Thm_ULHC_frame_latA
import Theorems.Thm_ULHC_frame_latB
import Theorems.Thm_ULHC_frame_opp
import Theorems.Thm_ULHC_ind_of_mem
import Theorems.Thm_ULHC_ind_of_not_mem
import Theorems.Thm_ULHC_outer1_body
import Theorems.Thm_ULHC_outer2_body
import Theorems.Thm_ULHC_strip_sig


set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
  {d u : Pt} {tf tu : Side} {x : Edge}
  (hb : back d tf ∈ F) (hxd : x ∈ F) (hxlat : x = lat1 d tf ∨ x = lat2 d tf)
  (hxl : (lat1 d tf ∈ F ∧ lat2 d tf ∉ F) ∨ (lat2 d tf ∈ F ∧ lat1 d tf ∉ F))
  (lu1 : lat1 u tu ∈ F) (lu2 : lat2 u tu ∈ F) (bu : back u tu ∉ F) (fu : front u tu ∉ F)
  (hxu : x ∈ cellE u) (hdu : d ≠ u)
include hF hT hk hcell hpat hsep hb hxd hxlat hxl hxu hdu
namespace ULHC
theorem _root_.solution (_hs : Solid V) (x0 : Pt) (_hconn : ∀ z ∈ V, Conn (GE V) x0 z)
    (hT' : NoTypeIII V (flipCol F c s (k + 2))) {m : ℕ} (hfr : front d tf ∈ F ↔ m = 1)
    (hd : d = nb (cellJ c s (k + 1)) s) :
    (tf = s.opp ∧ front d tf ∉ F) ∨
      (m = 1 ∧ u = nb d s ∧ lat1 d s ∈ F ∧ lat2 d s ∈ F ∧ front d s ∈ F) := by
  set e := cellJ c s (k + 1)
  obtain ⟨a1, a2, _, af⟩ := strip_sig hpat (show k + 1 < k + 2 by omega)
  have l1 : lat1 e s ∈ F := a1.2 (by omega)
  have l2 : lat2 e s ∈ F := a2.2 (by omega)
  have hfe : front e s ∉ F := fun h => by have := (af.1 h).1 (by omega); omega
  have hbd : back d s ∉ F := by rw [hd, back_nb]; exact hfe
  have hce := hcell (k + 1) le_rfl
  rcases start_frame s hb hxl with ⟨htp, _⟩ | ⟨ht, _, hbf⟩
  · rcases htp with rfl | rfl
    · exact absurd hb hbd
    · left; refine ⟨rfl, ?_⟩; rw [(frame_opp d s).2.2.2]; exact hbd
  · right
    have hfd : front d s ∈ F := by by_contra h; exact hbd (hbf.2 h)
    have hxf : x = front d s := by
      rcases perp_x hxlat ht with h | h
      · exact absurd (h ▸ hxd) hbd
      · exact h
    have hu' := u_across hxu hdu (show x = sideEdge d s from hxf)
    rcases ht with rfl | rfl
    · -- Frame `latA s`: back is `lat2 d s`, front is `lat1 d s`.
      --
      have hb2 : lat2 d s ∈ F := by rw [← (frame_latA d s).2.1]; exact hb
      by_cases hm : m = 1
      · exact ⟨hm, hu', by rw [← (frame_latA d s).1]; exact hfr.2 hm, hb2, hfd⟩
      · exfalso
        have hl1 : lat1 d s ∉ F := by rw [← (frame_latA d s).1]; exact fun h => hm (hfr.1 h)
        have hd1 := hF.2 _ (corners4 hce s).2.2.1
        rw [deg_front1, ind_of_mem l1, ind_of_not_mem hfe, ← hd, ind_of_not_mem hl1] at hd1
        have ho : outer1 e s ∈ F := by by_contra ho; rw [ind_of_not_mem ho] at hd1; omega
        have hb0 := (outer1_body hF hcell hpat le_rfl).2 hk
        exact beside_end1 hF hT hk hcell hpat hsep hb0 ho
          (end_side_far1 hF hT hk hcell hpat hb0 ho) hT'
    · have hb1 : lat1 d s ∈ F := by rw [← (frame_latB d s).2.1]; exact hb
      by_cases hm : m = 1
      · exact ⟨hm, hu', hb1, by rw [← (frame_latB d s).1]; exact hfr.2 hm, hfd⟩
      · exfalso
        have hl2 : lat2 d s ∉ F := by rw [← (frame_latB d s).1]; exact fun h => hm (hfr.1 h)
        have hd2 := hF.2 _ (corners4 hce s).2.2.2
        rw [deg_front2, ind_of_mem l2, ind_of_not_mem hfe, ← hd, ind_of_not_mem hl2] at hd2
        have ho : outer2 e s ∈ F := by by_contra ho; rw [ind_of_not_mem ho] at hd2; omega
        have hb0 := (outer2_body hF hcell hpat le_rfl).2 hk
        exact beside_end2 hF hT hk hcell hpat hsep hb0 ho
          (end_side_far2 hF hT hk hcell hpat hb0 ho) hT'
end ULHC
