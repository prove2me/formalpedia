-- Prove2me | solution 1 for ULHC.touch_beyond
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:38:33.728965+00:00
-- url     : https://prove2.me/submissions/bb42a35f-0f82-4c45-9235-fd771581687f

import Definitions.Def_ULHC_Near
import Definitions.Def_ULHC_Touch
import Theorems.Thm_ULHC_frame_opp
import Theorems.Thm_ULHC_frame_latA
import Theorems.Thm_ULHC_frame_latB
import Theorems.Thm_ULHC_strip_sig
import Theorems.Thm_ULHC_cell_prev
import Theorems.Thm_ULHC_ACell_ab
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_back_nb
import Theorems.Thm_ULHC_corners4
import Theorems.Thm_ULHC_deg_front1
import Theorems.Thm_ULHC_deg_front2
import Theorems.Thm_ULHC_ind_of_mem
import Theorems.Thm_ULHC_ind_of_not_mem
import Theorems.Thm_ULHC_latB_eq_opp
import Theorems.Thm_ULHC_nb_nb_opp
import Theorems.Thm_ULHC_opp_opp
import Theorems.Thm_ULHC_outer1_side_nb_next
import Theorems.Thm_ULHC_outer2_side_nb_next
import Theorems.Thm_ULHC_side_cases


set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
  {z : Pt} {tf : Side} {m i i0 : ℕ} (hz : SigFrom F z tf m i0) (hi0 : i0 ≤ i) (hi : i < m)
include hF hk hpat hcell hz hi0 hi
namespace ULHC
theorem _root_.solution (hpvs : tf = s → 1 ≤ i → i0 ≤ i - 1) (hpv2 : 2 ≤ i → i0 ≤ i - 1) (hq : cellJ z tf i = nb (cellJ c s (k + 1)) s) :
    (tf = s.opp ∧ i % 2 = 1 ∧ i + 1 = m) ∨ (tf = s.opp ∧ i % 2 = 0 ∧ i + 1 < m) ∨
      ((tf = latA s ∨ tf = latB s) ∧ i = 0) := by
  set e := cellJ c s (k + 1)
  obtain ⟨a1, a2, ab, af⟩ := strip_sig hpat (show k + 1 < k + 2 by omega)
  have l1 : lat1 e s ∈ F := a1.2 (by omega)
  have l2 : lat2 e s ∈ F := a2.2 (by omega)
  have hfe : front e s ∉ F := fun h => by have := (af.1 h).1 (by omega); omega
  have hbu : back (nb e s) s ∉ F := by rw [back_nb]; exact hfe
  obtain ⟨g1, g2, gb, gf⟩ := hz i hi0 hi
  rw [hq] at g1 g2 gb gf
  rcases side_cases s tf with h | h | h | h <;> rw [h] at g1 g2 gb gf
  · exfalso
    have ho : i % 2 = 1 := by have := mt gb.2 hbu; omega
    have hp := cell_prev (z := z) (tf := tf) (i := i) (by omega)
    rw [hq, h, nb_nb_opp] at hp
    obtain ⟨p1, _, _, _⟩ := hz (i - 1) (hpvs h (by omega)) (show i - 1 < m by omega)
    rw [h] at p1; rw [hp] at p1
    have := p1.1 l1; omega
  · obtain ⟨_, _, _, ff⟩ := frame_opp (nb e s) s
    rw [ff] at gf
    rcases Nat.mod_two_eq_zero_or_one i with h0 | h0
    · refine Or.inr (Or.inl ⟨h, h0, ?_⟩)
      by_contra hm; exact hbu (gf.2 ⟨fun h' => by omega, fun h' => absurd h' hm⟩)
    · refine Or.inl ⟨h, h0, ?_⟩
      by_contra hm; exact hbu (gf.2 ⟨fun _ => by omega, fun _ => h0⟩)
  · obtain ⟨_, fb, fl⟩ := frame_latA (nb e s) s
    rw [fb] at gb
    have he : i % 2 = 0 := by
      rcases fl with ⟨h1, _⟩ | ⟨_, h2⟩
      · rw [h1] at g1; have := mt g1.2 hbu; omega
      · rw [h2] at g2; have := mt g2.2 hbu; omega
    refine Or.inr (Or.inr ⟨Or.inl h, ?_⟩)
    by_contra h0
    exfalso
    have hl2u := gb.2 he
    have hp := cell_prev (z := z) (tf := tf) (i := i) (by omega)
    rw [hq, h, ← latB_eq_opp] at hp
    obtain ⟨p1, p2, _, _⟩ := hz (i - 1) (hpv2 (by omega)) (show i - 1 < m by omega)
    rw [h] at p1 p2; rw [hp] at p1 p2
    have hbP : back (nb (nb e s) (latB s)) s ∈ F := by
      obtain ⟨_, _, fl'⟩ := frame_latA (nb (nb e s) (latB s)) s
      rcases fl' with ⟨h1, _⟩ | ⟨_, h2⟩
      · rw [← h1]; exact p1.2 (by omega)
      · rw [← h2]; exact p2.2 (by omega)
    have ho : outer2 e s ∈ F := by rw [outer2_side_nb_next]; exact hbP
    have hd := hF.2 _ (corners4 (hcell (k + 1) le_rfl) s).2.2.2
    rw [deg_front2, ind_of_mem l2, ind_of_not_mem hfe, ind_of_mem hl2u, ind_of_mem ho] at hd
    omega
  · obtain ⟨_, fb, fl⟩ := frame_latB (nb e s) s
    rw [fb] at gb
    have he : i % 2 = 0 := by
      rcases fl with ⟨h1, _⟩ | ⟨_, h2⟩
      · rw [h1] at g1; have := mt g1.2 hbu; omega
      · rw [h2] at g2; have := mt g2.2 hbu; omega
    refine Or.inr (Or.inr ⟨Or.inr h, ?_⟩)
    by_contra h0
    exfalso
    have hl1u := gb.2 he
    have hp := cell_prev (z := z) (tf := tf) (i := i) (by omega)
    have hBA : (latB s).opp = latA s := by rw [latB_eq_opp, opp_opp]
    rw [hq, h, hBA] at hp
    obtain ⟨p1, p2, _, _⟩ := hz (i - 1) (hpv2 (by omega)) (show i - 1 < m by omega)
    rw [h] at p1 p2; rw [hp] at p1 p2
    have hbP : back (nb (nb e s) (latA s)) s ∈ F := by
      obtain ⟨_, _, fl'⟩ := frame_latB (nb (nb e s) (latA s)) s
      rcases fl' with ⟨h1, _⟩ | ⟨_, h2⟩
      · rw [← h1]; exact p1.2 (by omega)
      · rw [← h2]; exact p2.2 (by omega)
    have ho : outer1 e s ∈ F := by rw [outer1_side_nb_next]; exact hbP
    have hd := hF.2 _ (corners4 (hcell (k + 1) le_rfl) s).2.2.1
    rw [deg_front1, ind_of_mem l1, ind_of_not_mem hfe, ind_of_mem hl1u, ind_of_mem ho] at hd
    omega
end ULHC
