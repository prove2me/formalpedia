-- Prove2me | solution 1 for ULHC.side2_front
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:59:17.738247+00:00
-- url     : https://prove2.me/submissions/29072fdf-5c41-4db9-a0c3-d8c35d883715

import Definitions.Def_ULHC_Enum
import Definitions.Def_ULHC_L57
import Definitions.Def_ULHC_Created
import Definitions.Def_ULHC_Near
import Theorems.Thm_ULHC_outer2_side_nb


set_option autoImplicit true
open ULHC
open Finset
variable (c : Pt) (s : Side)
namespace ULHC
theorem _root_.solution : front (nb c (latB s)) s = outer2 c s := by
  rw [outer2_side_nb]; rfl
end ULHC
