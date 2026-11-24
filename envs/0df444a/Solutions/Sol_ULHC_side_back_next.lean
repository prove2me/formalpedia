-- Prove2me | solution 1 for ULHC.side_back_next
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:44:32.354745+00:00
-- url     : https://prove2.me/submissions/c5cd5494-b4c8-4b36-a1dc-8204cd58f0ef

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
import Theorems.Thm_ULHC_outer1_side_nb_next

set_option autoImplicit true
open ULHC
open Finset Classical
variable (c : Pt) (s : Side)
namespace ULHC
theorem _root_.solution : back (nb (nb c s) (latA s)) s = outer1 c s := by
  rw [outer1_side_nb_next]; rfl
end ULHC
