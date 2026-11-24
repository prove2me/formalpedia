-- Prove2me | solution 1 for ULHC.Ends.ne_at
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:20:34.111029+00:00
-- url     : https://prove2.me/submissions/73898230-f7c8-4fe9-81c6-0b4695808db6

import Definitions.Def_ULHC_Near
import Definitions.Def_ULHC_Stacked
import Theorems.Thm_ULHC_Ends_inc_iff
import Theorems.Thm_ULHC_Ends_ne


set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
namespace Ends
theorem _root_.solution {g g' : Edge} {x m m' : Pt} (h : Ends g x m) (h' : Ends g' m m')
    (hx : x ≠ m') : g ≠ g' := by
  intro heq
  subst heq
  rcases (h'.inc_iff x).1 ((h.inc_iff x).2 (Or.inl rfl)) with h1 | h1
  · exact h.ne h1
  · exact hx h1
end Ends
end ULHC
