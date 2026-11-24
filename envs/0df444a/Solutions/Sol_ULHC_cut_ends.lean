-- Prove2me | solution 1 for ULHC.cut_ends
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:41:39.723322+00:00
-- url     : https://prove2.me/submissions/003151a0-eba9-40e4-9499-ad83e3c6f796

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57

set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution {P : Finset Pt} {e : Edge} {a b : Pt} (h : Ends e a b) :
    Cut P e ↔ (a ∈ P ↔ b ∉ P) := by
  unfold Cut
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> (rw [h1, h2]; try tauto)
end ULHC
