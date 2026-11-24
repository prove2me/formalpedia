-- Prove2me | solution 1 for ULHC.lat2_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:20:39.193965+00:00
-- url     : https://prove2.me/submissions/ee0e1307-f97e-4c9e-a8c4-d534b7ba2e71

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_Walk

set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution (c : Pt) (s : Side) : lat2 c s = sideEdge c (latB s) := by cases s <;> rfl
end ULHC
