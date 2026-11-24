-- Prove2me | solution 1 for ULHC.start_beside2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:22:08.751532+00:00
-- url     : https://prove2.me/submissions/148c4fc6-c253-421d-8d0a-ab7c9d278013

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Definitions.Def_ULHC_NearCA
import Theorems.Thm_ULHC_start_frame
import Theorems.Thm_P2M_ULHC_body_not_alt__d3691623e2ed
import Theorems.Thm_ULHC_perp_x
import Theorems.Thm_ULHC_u_across
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_alt_frame
import Theorems.Thm_ULHC_frame_opp
import Theorems.Thm_ULHC_lat1_eq
import Theorems.Thm_ULHC_latB_opp_eq
import Theorems.Thm_ULHC_nb_cellJ
import Theorems.Thm_ULHC_nb_comm_lat
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
theorem _root_.solution {j : ℕ} (hj : j ≤ k) (hd : d = nb (cellJ c s j) (latB s)) :
    tf = s.opp ∧ j % 2 = 0 ∧ x = lat2 d s := by
  obtain ⟨fn, fb, ff⟩ := side2_facts hF hT hk hcell hpat hsep hj
  rw [← hd] at fn fb ff
  have afu := alt_frame s lu1 lu2 bu fu
  -- `u` is not one of the cells beside the body.
  --
  have notside : ∀ j' ≤ k + 1, u ≠ nb (cellJ c s j') (latB s) := by
    intro j' hj' he
    have af := alt_frame s lu1 lu2 bu fu
    rw [he] at af
    by_cases hj'k : j' ≤ k
    · obtain ⟨_, fb', ff'⟩ := side2_facts hF hT hk hcell hpat hsep hj'k
      have := af.1; rw [fb', ff'] at this; omega
    · obtain rfl : j' = k + 1 := by omega
      have fn' : lat1 (nb (cellJ c s (k + 1)) (latB s)) s ∈ F := by
        rw [side2_lat1]; exact (strip_sig hpat (show k + 1 < k + 2 by omega)).2.1.2 (by omega)
      have fb' : back (nb (cellJ c s (k + 1)) (latB s)) s ∈ F := by
        rw [show back (nb (cellJ c s (k + 1)) (latB s)) s = outer2 (cellJ c s k) s by
          rw [outer2_side_nb_next, nb_cellJ]; rfl]
        exact (outer2_body hF hcell hpat le_rfl).2 hk
      exact (af.2.2.1 fb') fn'
  rcases start_frame s hb hxl with ⟨htp, hdiff⟩ | ⟨ht, hlat, hbf⟩
  · -- Along `s`: the dark lateral side is the far one.
    --
    have hxs : x = lat1 d s ∨ x = lat2 d s := by
      rcases htp with rfl | rfl
      · exact hxlat
      · rwa [(frame_opp d s).1, (frame_opp d s).2.1] at hxlat
    have hxfar : x = lat2 d s := by
      rcases hxs with h | h
      · exfalso
        have hu' := u_across hxu hdu (show x = sideEdge d (latA s) by rw [h, lat1_eq])
        rw [hd, ← latB_opp_eq, nb_nb_opp] at hu'
        rw [hu'] at lu1 lu2 bu fu
        exact body_not_alt' hk hpat hj lu1 lu2 bu fu
      · exact h
    have hl2 : lat2 d s ∈ F := hxfar ▸ hxd
    have he : j % 2 = 0 := by
      have : lat1 d s ∉ F := fun h => hdiff.1 h hl2
      rw [fn] at this; omega
    refine ⟨?_, he, hxfar⟩
    rcases htp with rfl | rfl
    · exfalso; have := fb.1 hb; omega
    · rfl
  · exfalso
    rcases perp_x hxlat ht with hx' | hx'
    · have hu' := u_across hxu hdu (show x = sideEdge d s.opp from hx')
      have hjo : j % 2 = 1 := fb.1 (hx' ▸ hxd)
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rw [hd, side2_down] at hu'
      exact notside j' (by omega) hu'
    · have hu' := u_across hxu hdu (show x = sideEdge d s from hx')
      rw [hd, (nb_comm_lat c s j).2] at hu'
      exact notside (j + 1) (by omega) hu'
end ULHC
