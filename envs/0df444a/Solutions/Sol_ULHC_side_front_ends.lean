-- Prove2me | solution 1 for ULHC.side_front_ends
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:03:26.047835+00:00
-- url     : https://prove2.me/submissions/9b093470-4ee2-45ab-8c95-e865b9d318fd

import Definitions.Def_ULHC_Enum
import Definitions.Def_ULHC_L57
import Definitions.Def_ULHC_Created
import Definitions.Def_ULHC_Near
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_ends_front
import Theorems.Thm_ULHC_side_front
import Theorems.Thm_ULHC_side_front2


set_option autoImplicit true
open ULHC
open Finset
variable (c : Pt) (s : Side)
namespace ULHC
theorem _root_.solution : Ends (outer1 c s) (front1 (nb c (latA s)) s) (front1 c s) := by
  have := ends_front (nb c (latA s)) s
  rwa [side_front2, side_front] at this
end ULHC
