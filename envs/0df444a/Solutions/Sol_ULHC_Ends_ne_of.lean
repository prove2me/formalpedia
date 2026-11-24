-- Prove2me | solution 1 for ULHC.Ends.ne_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:52:22.797524+00:00
-- url     : https://prove2.me/submissions/4736a453-a77a-4d9a-bd8a-968e8f444b7d

import Definitions.Def_ULHC_Flip
import Definitions.Def_ULHC_AFlip
import Theorems.Thm_ULHC_Ends_inc_iff

set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
namespace Ends
theorem _root_.solution {e e' : Edge} {u v u' v' : Pt} (h : Ends e u v) (h' : Ends e' u' v')
    (h1 : v' ≠ u) (h2 : v' ≠ v) : e ≠ e' := by
  intro heq
  subst heq
  rcases (h.inc_iff v').1 ((h'.inc_iff v').2 (Or.inr rfl)) with h | h
  · exact h1 h
  · exact h2 h
end Ends
end ULHC
