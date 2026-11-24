-- Prove2me | solution 1 for ULHC.touch_side2_end
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:37:23.788444+00:00
-- url     : https://prove2.me/submissions/5d7dafa2-463a-479e-a5be-133f5e7a51b3

import Definitions.Def_ULHC_Near
import Definitions.Def_ULHC_Touch
import Theorems.Thm_ULHC_frame_opp
import Theorems.Thm_ULHC_frame_latA
import Theorems.Thm_ULHC_frame_latB
import Theorems.Thm_ULHC_strip_sig
import Theorems.Thm_ULHC_cont_of
import Theorems.Thm_ULHC_outer2_body
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_nb_cellJ
import Theorems.Thm_ULHC_outer2_side_nb_next
import Theorems.Thm_ULHC_side2_front
import Theorems.Thm_ULHC_side2_lat1
import Theorems.Thm_ULHC_side_cases


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
theorem _root_.solution (hq : cellJ z tf i = nb (cellJ c s (k + 1)) (latB s)) :
    (tf = s.opp ∧ i % 2 = 1 ∧ i + 1 < m) ∨
      (tf = latA s ∧ outer2 (cellJ c s (k + 1)) s ∈ F ∧
        lat2 (nb (cellJ c s (k + 1)) (latB s)) s ∉ F) := by
  set L := nb (cellJ c s (k + 1)) (latB s)
  have fn : lat1 L s ∈ F := by
    rw [side2_lat1]; exact (strip_sig hpat (show k + 1 < k + 2 by omega)).2.1.2 (by omega)
  have fb : back L s ∈ F := by
    rw [show back L s = outer2 (cellJ c s k) s by rw [outer2_side_nb_next, nb_cellJ]; rfl]
    exact (outer2_body hF hcell hpat le_rfl).2 hk
  obtain ⟨g1, g2, gb, gf⟩ := hz i hi0 hi
  rw [hq] at g1 g2 gb gf
  rcases side_cases s tf with h | h | h | h <;> rw [h] at g1 g2 gb gf
  · exfalso; have := g1.1 fn; have := gb.1 fb; omega
  · obtain ⟨f1, _, _, ff'⟩ := frame_opp L s
    rw [f1] at g1; rw [ff'] at gf
    have ho := g1.1 fn
    exact Or.inl ⟨h, ho, cont_of gf ⟨fun _ => ho, fun _ => fb⟩⟩
  · obtain ⟨_, fbk, fl⟩ := frame_latA L s
    rw [fbk] at gb
    have ho : i % 2 = 1 := by
      rcases fl with ⟨h1, _⟩ | ⟨_, h2⟩
      · rw [h1] at g1; exact g1.1 fb
      · rw [h2] at g2; exact g2.1 fb
    refine Or.inr ⟨h, ?_, fun h' => by have := gb.1 h'; omega⟩
    rw [← side2_front]
    rcases fl with ⟨_, h2⟩ | ⟨h1, _⟩
    · rw [h2] at g2; exact g2.2 ho
    · rw [h1] at g1; exact g1.2 ho
  · exfalso
    obtain ⟨_, fbk, fl⟩ := frame_latB L s
    rw [fbk] at gb
    have he := gb.1 fn
    rcases fl with ⟨h1, _⟩ | ⟨_, h2⟩
    · rw [h1] at g1; have := g1.1 fb; omega
    · rw [h2] at g2; have := g2.1 fb; omega
end ULHC
