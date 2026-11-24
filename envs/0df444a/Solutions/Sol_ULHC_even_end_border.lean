-- Prove2me | solution 1 for ULHC.even_end_border
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:29:51.824853+00:00
-- url     : https://prove2.me/submissions/716d8792-5ada-4d54-a94a-5f4045dfec84

import Definitions.Def_ULHC_TheoremA
import Definitions.Def_ULHC_V2
import Theorems.Thm_ULHC_end_not_mid
import Theorems.Thm_ULHC_strip_even_rel
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_Ends_conn
import Theorems.Thm_ULHC_ends_lat1


set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {c : Pt} {s : Side}
namespace ULHC
theorem _root_.solution (k : ℕ) (hk : k % 2 = 0) (F : Finset Edge) (hF : Deg2 V F)
    (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
    (hsep : ¬ Conn F (back1 c s) (front1 c s))
    (hsame : Conn F (back1 (cellJ c s (k + 1)) s) (back2 (cellJ c s (k + 1)) s)) :
    ¬ Conn (flipCol F c s (k + 2)) (back1 (cellJ c s (k + 1)) s) (front1 (cellJ c s (k + 1)) s) := by
  obtain ⟨F1, _, _, hab, hrel, _, hodd⟩ := strip_even_rel k hk F hF hcell hpat hsep hsame
  obtain ⟨na, nb⟩ := end_not_mid c s k
  rw [hodd _ _ na nb]
  -- `back1 u ~ front1 u` in `F` (the end cell's dark lateral side).
  have huF : Conn F (back1 (cellJ c s (k + 1)) s) (front1 (cellJ c s (k + 1)) s) := by
    obtain ⟨_, hl, _⟩ := hpat
    exact (ends_lat1 _ s).conn ((hl (k + 1) (by omega)).1.2 (by omega))
  rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
  · exact hab h
  · exact hsep ((hrel _ _ h1).symm.trans (huF.trans (hrel _ _ h2).symm))
  · exact hsep ((hrel _ _ h2).trans (huF.symm.trans (hrel _ _ h1)))
end ULHC
