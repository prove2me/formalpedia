-- Prove2me | solution 1 for ULHC.touch_behind
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:23:28.75655+00:00
-- url     : https://prove2.me/submissions/d619ba79-072d-4a25-a48d-19a10899535b

import Definitions.Def_ULHC_Near
import Definitions.Def_ULHC_Touch
import Theorems.Thm_ULHC_frame_opp
import Theorems.Thm_ULHC_frame_latA
import Theorems.Thm_ULHC_frame_latB
import Theorems.Thm_ULHC_front_nb_opp
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_back_down
import Theorems.Thm_ULHC_back_down2
import Theorems.Thm_ULHC_cellJ_zero
import Theorems.Thm_ULHC_side_cases


set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
  {z : Pt} {tf : Side} {m i i0 : ℕ} (hz : SigFrom F z tf m i0) (hi0 : i0 ≤ i) (hi : i < m)
include hF hT hk hcell hpat hsep hz hi0 hi
namespace ULHC
theorem _root_.solution (hq : cellJ z tf i = nb c s.opp) : tf = s ∧ i % 2 = 1 ∧ i + 1 < m := by
  have hc0 : IsCell V c := by have := hcell 0 (by omega); rwa [cellJ_zero] at this
  have h2 : 2 ≤ k + 2 := by omega
  have d1 := back_down hF hT hpat h2 hc0 hsep
  have d2 := back_down2 hF hT hpat h2 hc0 hsep
  have df : front (nb c s.opp) s ∈ F := by rw [front_nb_opp]; exact hpat.1
  obtain ⟨g1, g2, gb, gf⟩ := hz i hi0 hi
  rw [hq] at g1 g2 gb gf
  rcases side_cases s tf with h | h | h | h <;> rw [h] at g1 g2 gb gf
  · have hodd := g1.1 d1
    exact ⟨h, hodd, (gf.1 df).1 hodd⟩
  · obtain ⟨f1, _, fb, _⟩ := frame_opp (nb c s.opp) s
    rw [f1] at g1; rw [fb] at gb
    have := g1.1 d1; have := gb.1 df; omega
  · obtain ⟨_, fb, fl⟩ := frame_latA (nb c s.opp) s
    rw [fb] at gb
    have he := gb.1 d2
    rcases fl with ⟨_, h'⟩ | ⟨h', _⟩
    · rw [h'] at g2; have := g2.1 df; omega
    · rw [h'] at g1; have := g1.1 df; omega
  · obtain ⟨_, fb, fl⟩ := frame_latB (nb c s.opp) s
    rw [fb] at gb
    have he := gb.1 d1
    rcases fl with ⟨_, h'⟩ | ⟨h', _⟩
    · rw [h'] at g2; have := g2.1 df; omega
    · rw [h'] at g1; have := g1.1 df; omega
end ULHC
