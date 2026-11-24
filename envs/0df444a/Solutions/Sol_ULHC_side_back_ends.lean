-- Prove2me | solution 1 for ULHC.side_back_ends
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:19:41.412043+00:00
-- url     : https://prove2.me/submissions/5975857e-69aa-467c-ae17-495f8aef3c71

import Definitions.Def_ULHC_Enum
import Definitions.Def_ULHC_L57
import Definitions.Def_ULHC_Created
import Definitions.Def_ULHC_Near
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_ends_back
import Theorems.Thm_ULHC_side_back2


set_option autoImplicit true
open ULHC
open Finset
variable (c : Pt) (s : Side)
namespace ULHC
theorem _root_.solution : Ends (back (nb c (latA s)) s) (back1 (nb c (latA s)) s) (back1 c s) := by
  have := ends_back (nb c (latA s)) s
  rwa [side_back2] at this
end ULHC
