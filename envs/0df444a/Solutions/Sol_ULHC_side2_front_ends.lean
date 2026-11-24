-- Prove2me | solution 1 for ULHC.side2_front_ends
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:19:46.160199+00:00
-- url     : https://prove2.me/submissions/02d4acd9-629d-4236-8283-1469909a64f9

import Definitions.Def_ULHC_Enum
import Definitions.Def_ULHC_L57
import Definitions.Def_ULHC_Created
import Definitions.Def_ULHC_Near
import Theorems.Thm_ULHC_side2_front1
import Theorems.Thm_ULHC_side2_front
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_ends_front


set_option autoImplicit true
open ULHC
open Finset
variable (c : Pt) (s : Side)
namespace ULHC
theorem _root_.solution : Ends (outer2 c s) (front2 c s) (front2 (nb c (latB s)) s) := by
  have := ends_front (nb c (latB s)) s
  rwa [side2_front1, side2_front] at this
end ULHC
