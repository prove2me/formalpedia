-- Prove2me | solution 1 for ULHC.osi_far
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:00:01.882115+00:00
-- url     : https://prove2.me/submissions/4d21e609-5d9e-406b-8809-da5b2ebb9cfd

import Definitions.Def_ULHC_Created
import Definitions.Def_ULHC_Cr2
import Theorems.Thm_ULHC_osi_split
import Theorems.Thm_ULHC_APair_flip
import Theorems.Thm_ULHC_strip_even_rel


set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {G : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hG : Deg2 V G) (hk : k % 2 = 0) (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j))
  (hpat : StripPat G c s (k + 2)) (hsep : ¬ Conn G (back1 c s) (front1 c s))
  (hsame : Conn G (back1 (cellJ c s (k + 1)) s) (back2 (cellJ c s (k + 1)) s))
  (hT' : NoTypeIII V (flipCol G c s (k + 2)))
include hG hk hcell hpat hsep hsame hT'
namespace ULHC
theorem _root_.solution {u : Pt} {tf : Side} (hu : IsCell V u)
    (lu1 : lat1 u tf ∈ G) (lu2 : lat2 u tf ∈ G) (bu : back u tf ∉ G) (fu : front u tf ∉ G)
    (hsu : Conn G (back1 u tf) (back2 u tf))
    (hfar : ∀ j ≤ k + 1, ∀ e ∈ cellE u, e ∉ cellE (cellJ c s j))
    (hmu1 : ¬ IsMid c s k (back1 u tf)) (hmu2 : ¬ IsMid c s k (back2 u tf))
    {x y : Pt} (hxy : Conn G x y) (hsplit : ¬ Conn (flip G u) x y)
    (hx : ¬ IsMid c s k x) (hy : ¬ IsMid c s k y) :
    (Conn (flipCol G c s (k + 2)) x y ∧ ¬ Conn (flip (flipCol G c s (k + 2)) u) x y) ∨
      ¬ Conn (flip G (cellJ c s (k + 1))) x y := by
  obtain ⟨F1, hF1, _, _, hrel, _, hodd⟩ := strip_even_rel k hk G hG hcell hpat hsep hsame
  by_cases hC : Conn (flipCol G c s (k + 2)) x y
  · exact Or.inl ⟨hC, osi_split hG hk hcell hpat hsep hsame hT' hu lu1 lu2 bu fu hsu hfar hmu1 hmu2
      hxy hsplit hx hy⟩
  · right
    intro h; exact hC ((hodd x y hx hy).2 (Or.inl (hF1 ▸ h)))
end ULHC
