-- Prove2me | solution 1 for ULHC.side2_back_ends
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:24:26.612372+00:00
-- url     : https://prove2.me/submissions/a5752063-0a94-4734-b12d-706bf8740858

import Definitions.Def_ULHC_Enum
import Definitions.Def_ULHC_L57
import Definitions.Def_ULHC_Created
import Definitions.Def_ULHC_Near
import Theorems.Thm_ULHC_side2_back1
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_ends_back


set_option autoImplicit true
open ULHC
open Finset
variable (c : Pt) (s : Side)
namespace ULHC
theorem _root_.solution : Ends (back (nb c (latB s)) s) (back2 c s) (back2 (nb c (latB s)) s) := by
  have := ends_back (nb c (latB s)) s
  rwa [side2_back1] at this
end ULHC
