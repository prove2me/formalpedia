-- Prove2me | solution 1 for ULHC.alt_touch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:22:07.347154+00:00
-- url     : https://prove2.me/submissions/c708609c-eddb-4364-832a-32e499786ac0

import Definitions.Def_ULHC_NearChain
import Definitions.Def_ULHC_NearLemma
import Theorems.Thm_ULHC_cellJ_down
import Theorems.Thm_ULHC_alt_frame
import Theorems.Thm_ULHC_body_not_alt
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_back_down
import Theorems.Thm_ULHC_cellJ_zero
import Theorems.Thm_ULHC_front_nb_opp
import Theorems.Thm_ULHC_nb_cellJ
import Theorems.Thm_ULHC_outer1_body
import Theorems.Thm_ULHC_outer2_body
import Theorems.Thm_ULHC_outer2_side_nb_next
import Theorems.Thm_ULHC_side1_facts
import Theorems.Thm_ULHC_side2_facts
import Theorems.Thm_ULHC_side2_lat1
import Theorems.Thm_ULHC_side_back_next
import Theorems.Thm_ULHC_side_lat2
import Theorems.Thm_ULHC_strip_sig
import Theorems.Thm_ULHC_touch_cases


set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hs : Solid V) (x0 : Pt) (hconn : ∀ z ∈ V, Conn (GE V) x0 z)
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s)) (hT' : NoTypeIII V (flipCol F c s (k + 2)))
  {z : Pt} {tf : Side} {m : ℕ} (hz : StripPat F z tf m)
include hs x0 hconn hF hT hk hcell hpat hsep hT' hz
omit hs hconn hT' hz
omit x0
namespace ULHC
theorem _root_.solution {w : Pt} {tw : Side} (l1 : lat1 w tw ∈ F) (l2 : lat2 w tw ∈ F)
    (bw : back w tw ∉ F) (fw : front w tw ∉ F) {j : ℕ} (hj : j < k + 2) {x : Edge}
    (hx1 : x ∈ cellE w) (hx2 : x ∈ cellE (cellJ c s j)) :
    w = cellJ c s (k + 1) ∨ w = nb (cellJ c s (k + 1)) s := by
  have af := alt_frame s l1 l2 bw fw
  have body : ∀ j' ≤ k + 1, w = cellJ c s j' → w = cellJ c s (k + 1) := by
    intro j' hj' hw
    by_cases h : j' = k + 1
    · rw [hw, h]
    · rw [hw] at l1 l2 bw fw
      exact (body_not_alt hk hpat (by omega) l1 l2 bw fw).elim
  rcases touch_cases s hx1 hx2 with hq | hq | hq | hq | hq
  · exact Or.inl (body j (by omega) hq)
  · by_cases hjk : j ≤ k
    · exact Or.inl (body (j + 1) (by omega) (by rw [hq, nb_cellJ]))
    · exact Or.inr (by rw [hq, show j = k + 1 by omega])
  · rcases j with _ | j
    · exfalso
      rw [cellJ_zero] at hq
      have hc0 : IsCell V c := by have := hcell 0 (by omega); rwa [cellJ_zero] at this
      have d1 := back_down hF hT hpat (by omega) hc0 hsep
      have df : front (nb c s.opp) s ∈ F := by rw [front_nb_opp]; exact hpat.1
      rw [← hq] at d1 df
      have := af.2.2; have := af.1; tauto
    · exact Or.inl (body j (by omega) (by rw [hq, cellJ_down]))
  · exfalso
    by_cases hjk : j ≤ k
    · obtain ⟨_, fb, ff⟩ := side1_facts hF hT hk hcell hpat hsep hjk
      rw [← hq] at fb ff
      have := af.1; rw [fb, ff] at this; omega
    · obtain rfl : j = k + 1 := by omega
      have fn : lat2 w s ∈ F := by
        rw [hq, side_lat2]; exact (strip_sig hpat (show k + 1 < k + 2 by omega)).1.2 (by omega)
      have fb : back w s ∈ F := by
        rw [hq, show back (nb (cellJ c s (k + 1)) (latA s)) s = outer1 (cellJ c s k) s by
          rw [← side_back_next, nb_cellJ]]
        exact (outer1_body hF hcell hpat le_rfl).2 hk
      have := af.2.1; have := af.2.2; tauto
  · exfalso
    by_cases hjk : j ≤ k
    · obtain ⟨_, fb, ff⟩ := side2_facts hF hT hk hcell hpat hsep hjk
      rw [← hq] at fb ff
      have := af.1; rw [fb, ff] at this; omega
    · obtain rfl : j = k + 1 := by omega
      have fn : lat1 w s ∈ F := by
        rw [hq, side2_lat1]; exact (strip_sig hpat (show k + 1 < k + 2 by omega)).2.1.2 (by omega)
      have fb : back w s ∈ F := by
        rw [hq, show back (nb (cellJ c s (k + 1)) (latB s)) s = outer2 (cellJ c s k) s by
          rw [outer2_side_nb_next, nb_cellJ]; rfl]
        exact (outer2_body hF hcell hpat le_rfl).2 hk
      have := af.2.1; have := af.2.2; tauto
end ULHC
