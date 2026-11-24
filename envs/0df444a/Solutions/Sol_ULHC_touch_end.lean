-- Prove2me | solution 1 for ULHC.touch_end
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:38:21.476147+00:00
-- url     : https://prove2.me/submissions/b2e439fe-d22c-4c1e-8712-bfcc4cdf8aea

import Definitions.Def_ULHC_Near
import Definitions.Def_ULHC_Touch
import Theorems.Thm_ULHC_frame_opp
import Theorems.Thm_ULHC_frame_latA
import Theorems.Thm_ULHC_frame_latB
import Theorems.Thm_ULHC_strip_sig
import Theorems.Thm_ULHC_ACell_ab
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_side_cases


set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
  {z : Pt} {tf : Side} {m i i0 : ℕ} (hz : SigFrom F z tf m i0) (hi0 : i0 ≤ i) (hi : i < m)
include hk hpat hz hi0 hi
namespace ULHC
theorem _root_.solution (hq : cellJ z tf i = cellJ c s (k + 1)) :
    i + 1 = m ∧ (((tf = s ∨ tf = s.opp) ∧ i % 2 = 1) ∨ ((tf = latA s ∨ tf = latB s) ∧ i % 2 = 0)) := by
  obtain ⟨g1, g2, gb, gf⟩ := hz i hi0 hi
  obtain ⟨a1, a2, ab, af⟩ := strip_sig hpat (show k + 1 < k + 2 by omega)
  rw [hq] at g1 g2 gb gf
  have l1 := a1.2 (by omega)
  have l2 := a2.2 (by omega)
  have hb' : back (cellJ c s (k + 1)) s ∉ F := fun h => by have := ab.1 h; omega
  have hf' : front (cellJ c s (k + 1)) s ∉ F := fun h => by have := (af.1 h).1 (by omega); omega
  rcases side_cases s tf with h | h | h | h <;> rw [h] at g1 g2 gb gf
  · have ho := g1.1 l1
    refine ⟨?_, Or.inl ⟨Or.inl h, ho⟩⟩
    by_contra hm
    exact hf' (gf.2 ⟨fun _ => by omega, fun _ => ho⟩)
  · obtain ⟨f1, _, _, ff⟩ := frame_opp (cellJ c s (k + 1)) s
    rw [f1] at g1; rw [ff] at gf
    have ho := g1.1 l1
    refine ⟨?_, Or.inl ⟨Or.inr h, ho⟩⟩
    by_contra hm
    exact hb' (gf.2 ⟨fun _ => by omega, fun _ => ho⟩)
  · obtain ⟨ff, _, fl⟩ := frame_latA (cellJ c s (k + 1)) s
    rw [ff] at gf
    have he : i % 2 = 0 := by
      rcases fl with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] at g1
      · have := mt g1.2 hb'; omega
      · have := mt g1.2 hf'; omega
    refine ⟨?_, Or.inr ⟨Or.inl h, he⟩⟩
    have := (gf.1 l1); by_contra hm
    have := this.2 (by omega); omega
  · obtain ⟨ff, _, fl⟩ := frame_latB (cellJ c s (k + 1)) s
    rw [ff] at gf
    have he : i % 2 = 0 := by
      rcases fl with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] at g1
      · have := mt g1.2 hb'; omega
      · have := mt g1.2 hf'; omega
    refine ⟨?_, Or.inr ⟨Or.inr h, he⟩⟩
    have := (gf.1 l2); by_contra hm
    have := this.2 (by omega); omega
end ULHC
