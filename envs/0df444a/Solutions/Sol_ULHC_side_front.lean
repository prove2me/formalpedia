-- Prove2me | solution 1 for ULHC.side_front
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:44:35.212793+00:00
-- url     : https://prove2.me/submissions/8125230d-9131-43f8-b9b4-e022b846641d

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
import Theorems.Thm_ULHC_outer1_side_nb

set_option autoImplicit true
open ULHC
open Finset Classical
variable (c : Pt) (s : Side)
namespace ULHC
theorem _root_.solution : front (nb c (latA s)) s = outer1 c s := by
  rw [outer1_side_nb]; rfl
end ULHC
