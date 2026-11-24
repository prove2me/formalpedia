-- Prove2me | solution 1 for ULHC.start_beside_end2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:22:09.2748+00:00
-- url     : https://prove2.me/submissions/860c62f4-dca6-49f5-ad5e-d50b29a4295a

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Definitions.Def_ULHC_NearCA
import Theorems.Thm_ULHC_start_frame
import Theorems.Thm_ULHC_perp_x
import Theorems.Thm_ULHC_u_across
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_alt_frame
import Theorems.Thm_ULHC_frame_opp
import Theorems.Thm_ULHC_lat1_eq
import Theorems.Thm_ULHC_latB_opp_eq
import Theorems.Thm_ULHC_nb_cellJ
import Theorems.Thm_ULHC_nb_nb_opp
import Theorems.Thm_ULHC_outer2_body
import Theorems.Thm_ULHC_outer2_side_nb_next
import Theorems.Thm_ULHC_side2_down
import Theorems.Thm_ULHC_side2_facts
import Theorems.Thm_ULHC_side2_lat1
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
include hF hT hk hcell hpat hsep hb hxd hxlat hxl lu1 lu2 bu fu hxu hdu
namespace ULHC
theorem _root_.solution (hd : d = nb (cellJ c s (k + 1)) (latB s)) :
    u = cellJ c s (k + 1) ∧ (tf = s ∨ (tf = s.opp ∧ front d tf ∈ F)) := by
  have fn : lat1 d s ∈ F := by
    rw [hd, side2_lat1]; exact (strip_sig hpat (show k + 1 < k + 2 by omega)).2.1.2 (by omega)
  have fb : back d s ∈ F := by
    rw [hd, show back (nb (cellJ c s (k + 1)) (latB s)) s = outer2 (cellJ c s k) s by
      rw [outer2_side_nb_next, nb_cellJ]; rfl]
    exact (outer2_body hF hcell hpat le_rfl).2 hk
  rcases start_frame s hb hxl with ⟨htp, hdiff⟩ | ⟨ht, _, hbf⟩
  · have hxs : x = lat1 d s ∨ x = lat2 d s := by
      rcases htp with rfl | rfl
      · exact hxlat
      · rwa [(frame_opp d s).1, (frame_opp d s).2.1] at hxlat
    have hl2 : lat2 d s ∉ F := hdiff.1 fn
    have hx1 : x = lat1 d s := by
      rcases hxs with h | h
      · exact h
      · exact absurd (h ▸ hxd) hl2
    have hu' := u_across hxu hdu (show x = sideEdge d (latA s) by rw [hx1, lat1_eq])
    rw [hd, ← latB_opp_eq, nb_nb_opp] at hu'
    refine ⟨hu', ?_⟩
    rcases htp with h | h
    · exact Or.inl h
    · right; refine ⟨h, ?_⟩; rw [h, (frame_opp d s).2.2.2]; exact fb
  · exfalso
    have hfF : front d s ∉ F := fun h => (hbf.1 fb) h
    have hxb : x = back d s := by
      rcases perp_x hxlat ht with h | h
      · exact h
      · exact absurd (h ▸ hxd) hfF
    have hu' := u_across hxu hdu (show x = sideEdge d s.opp from hxb)
    rw [hd, side2_down] at hu'
    obtain ⟨_, fb', ff'⟩ := side2_facts hF hT hk hcell hpat hsep (le_refl k)
    have af := alt_frame s lu1 lu2 bu fu
    rw [hu'] at af
    have := af.1; rw [fb', ff'] at this; omega
end ULHC
