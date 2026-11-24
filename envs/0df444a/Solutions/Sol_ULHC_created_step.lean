-- Prove2me | solution 1 for ULHC.created_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:56:50.104791+00:00
-- url     : https://prove2.me/submissions/37e44a7c-1bff-471e-9054-9b0898c1d8e3

import Definitions.Def_ULHC_Created
import Definitions.Def_ULHC_Cr2
import Theorems.Thm_ULHC_APair_flip
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_DWalk_trans
import Theorems.Thm_ULHC_PStep_symm
import Theorems.Thm_ULHC_strip_even_rel


set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {G : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
namespace ULHC
theorem _root_.solution (hk : k % 2 = 0) (hG : Deg2 V G)
    (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat G c s (k + 2))
    (hsep : ¬ Conn G (back1 c s) (front1 c s))
    (hsame : Conn G (back1 (cellJ c s (k + 1)) s) (back2 (cellJ c s (k + 1)) s))
    {x y : Pt} (hxy : Conn G x y) (hsplit : ¬ Conn (flip G (cellJ c s (k + 1))) x y)
    (hx : ¬ IsMid c s k x) (hy : ¬ IsMid c s k y) :
    ¬ Conn (flipCol G c s (k + 2)) x y := by
  obtain ⟨F1, hF1, _, _, hrel, _, hodd⟩ := strip_even_rel k hk G hG hcell hpat hsep hsame
  rw [hodd x y hx hy]
  subst hF1
  rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
  · exact hsplit h
  · exact hsep (((hrel _ _ h1).symm.trans hxy).trans (hrel _ _ h2).symm)
  · exact hsep (((hrel _ _ h2).trans hxy.symm).trans (hrel _ _ h1))
end ULHC
