-- Prove2me | solution 1 for ULHC.start_beside1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:17:03.786498+00:00
-- url     : https://prove2.me/submissions/b583c265-18b4-47f6-8ade-892877cd6bd0

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
import Theorems.Thm_ULHC_lat2_eq
import Theorems.Thm_ULHC_latB_eq_opp
import Theorems.Thm_ULHC_nb_cellJ
import Theorems.Thm_ULHC_nb_comm_lat
import Theorems.Thm_ULHC_nb_nb_opp
import Theorems.Thm_ULHC_outer1_body
import Theorems.Thm_ULHC_side1_down
import Theorems.Thm_ULHC_side1_facts
import Theorems.Thm_ULHC_side_back_next
import Theorems.Thm_ULHC_side_lat2
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
theorem _root_.solution {j : ℕ} (hj : j ≤ k) (hd : d = nb (cellJ c s j) (latA s)) :
    tf = s.opp ∧ j % 2 = 0 ∧ x = lat1 d s := by
  obtain ⟨fn, fb, ff⟩ := side1_facts hF hT hk hcell hpat hsep hj
  rw [← hd] at fn fb ff
  have afu := alt_frame s lu1 lu2 bu fu
  -- `u` is not one of the cells beside the body.
  --
  have notside : ∀ j' ≤ k + 1, u ≠ nb (cellJ c s j') (latA s) := by
    intro j' hj' he
    have af := alt_frame s lu1 lu2 bu fu
    rw [he] at af
    by_cases hj'k : j' ≤ k
    · obtain ⟨_, fb', ff'⟩ := side1_facts hF hT hk hcell hpat hsep hj'k
      have := af.1; rw [fb', ff'] at this; omega
    · obtain rfl : j' = k + 1 := by omega
      have fn' : lat2 (nb (cellJ c s (k + 1)) (latA s)) s ∈ F := by
        rw [side_lat2]; exact (strip_sig hpat (show k + 1 < k + 2 by omega)).1.2 (by omega)
      have fb' : back (nb (cellJ c s (k + 1)) (latA s)) s ∈ F := by
        rw [show back (nb (cellJ c s (k + 1)) (latA s)) s = outer1 (cellJ c s k) s by
          rw [← side_back_next, nb_cellJ]]
        exact (outer1_body hF hcell hpat le_rfl).2 hk
      exact (af.2.2.1 fb') (af.2.1.2 fn')
  rcases start_frame s hb hxl with ⟨htp, hdiff⟩ | ⟨ht, hlat, hbf⟩
  · -- Along `s`: the dark lateral side is the far one.
    --
    have hxs : x = lat1 d s ∨ x = lat2 d s := by
      rcases htp with rfl | rfl
      · exact hxlat
      · rwa [(frame_opp d s).1, (frame_opp d s).2.1] at hxlat
    have hxfar : x = lat1 d s := by
      rcases hxs with h | h
      · exact h
      · exfalso
        have hu' := u_across hxu hdu (show x = sideEdge d (latB s) by rw [h, lat2_eq])
        rw [hd, latB_eq_opp, nb_nb_opp] at hu'
        rw [hu'] at lu1 lu2 bu fu
        exact body_not_alt' hk hpat hj lu1 lu2 bu fu
    have hl1 : lat1 d s ∈ F := hxfar ▸ hxd
    have he : j % 2 = 0 := by
      have := hdiff.1 hl1; rw [fn] at this; omega
    refine ⟨?_, he, hxfar⟩
    rcases htp with rfl | rfl
    · exfalso; have := fb.1 hb; omega
    · rfl
  · exfalso
    rcases perp_x hxlat ht with hx' | hx'
    · have hu' := u_across hxu hdu (show x = sideEdge d s.opp from hx')
      have hjo : j % 2 = 1 := fb.1 (hx' ▸ hxd)
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rw [hd, side1_down] at hu'
      exact notside j' (by omega) hu'
    · have hu' := u_across hxu hdu (show x = sideEdge d s from hx')
      rw [hd, (nb_comm_lat c s j).1] at hu'
      exact notside (j + 1) (by omega) hu'
end ULHC
