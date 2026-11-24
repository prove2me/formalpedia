-- Prove2me | solution 1 for ULHC.touch_side1_end
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:36:21.776236+00:00
-- url     : https://prove2.me/submissions/22bad001-2a08-4ca3-b9eb-d855abb92cc3

import Definitions.Def_ULHC_Near
import Definitions.Def_ULHC_Touch
import Theorems.Thm_ULHC_frame_opp
import Theorems.Thm_ULHC_frame_latA
import Theorems.Thm_ULHC_frame_latB
import Theorems.Thm_ULHC_strip_sig
import Theorems.Thm_ULHC_cont_of
import Theorems.Thm_ULHC_outer1_body
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_nb_cellJ
import Theorems.Thm_ULHC_side_back_next
import Theorems.Thm_ULHC_side_cases
import Theorems.Thm_ULHC_side_front
import Theorems.Thm_ULHC_side_lat2


set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
  {z : Pt} {tf : Side} {m i i0 : ℕ} (hz : SigFrom F z tf m i0) (hi0 : i0 ≤ i) (hi : i < m)
include hF hk hcell hpat hz hi0 hi
namespace ULHC
theorem _root_.solution (hq : cellJ z tf i = nb (cellJ c s (k + 1)) (latA s)) :
    (tf = s.opp ∧ i % 2 = 1 ∧ i + 1 < m) ∨
      (tf = latB s ∧ outer1 (cellJ c s (k + 1)) s ∈ F ∧
        lat1 (nb (cellJ c s (k + 1)) (latA s)) s ∉ F) := by
  set L := nb (cellJ c s (k + 1)) (latA s)
  have fn : lat2 L s ∈ F := by
    rw [side_lat2]; exact (strip_sig hpat (show k + 1 < k + 2 by omega)).1.2 (by omega)
  have fb : back L s ∈ F := by
    rw [show back L s = outer1 (cellJ c s k) s by rw [← side_back_next, nb_cellJ]]
    exact (outer1_body hF hcell hpat le_rfl).2 hk
  obtain ⟨g1, g2, gb, gf⟩ := hz i hi0 hi
  rw [hq] at g1 g2 gb gf
  rcases side_cases s tf with h | h | h | h <;> rw [h] at g1 g2 gb gf
  · exfalso; have := g2.1 fn; have := gb.1 fb; omega
  · obtain ⟨_, f2, _, ff'⟩ := frame_opp L s
    rw [f2] at g2; rw [ff'] at gf
    have ho := g2.1 fn
    exact Or.inl ⟨h, ho, cont_of gf ⟨fun _ => ho, fun _ => fb⟩⟩
  · exfalso
    obtain ⟨_, fbk, fl⟩ := frame_latA L s
    rw [fbk] at gb
    have he := gb.1 fn
    rcases fl with ⟨h1, _⟩ | ⟨_, h2⟩
    · rw [h1] at g1; have := g1.1 fb; omega
    · rw [h2] at g2; have := g2.1 fb; omega
  · obtain ⟨_, fbk, fl⟩ := frame_latB L s
    rw [fbk] at gb
    have ho : i % 2 = 1 := by
      rcases fl with ⟨h1, _⟩ | ⟨_, h2⟩
      · rw [h1] at g1; exact g1.1 fb
      · rw [h2] at g2; exact g2.1 fb
    refine Or.inr ⟨h, ?_, fun h' => by have := gb.1 h'; omega⟩
    rw [← side_front]
    rcases fl with ⟨_, h2⟩ | ⟨h1, _⟩
    · rw [h2] at g2; exact g2.2 ho
    · rw [h1] at g1; exact g1.2 ho
end ULHC
