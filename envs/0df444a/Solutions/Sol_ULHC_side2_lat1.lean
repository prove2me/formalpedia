-- Prove2me | solution 1 for ULHC.side2_lat1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:43:02.105032+00:00
-- url     : https://prove2.me/submissions/bedac6d2-b36b-4d57-addb-c88ac87b6606

import Definitions.Def_ULHC_Enum
import Definitions.Def_ULHC_L57
import Definitions.Def_ULHC_Created
import Definitions.Def_ULHC_Near
import Theorems.Thm_ULHC_lat1_eq
import Theorems.Thm_ULHC_lat2_side_nb


set_option autoImplicit true
open ULHC
open Finset
variable (c : Pt) (s : Side)
namespace ULHC
theorem _root_.solution : lat1 (nb c (latB s)) s = lat2 c s := by
  rw [lat2_side_nb, lat1_eq]
  cases s <;> rfl
end ULHC
