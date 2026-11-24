-- Prove2me | solution 1 for ULHC.lat1_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:20:02.577978+00:00
-- url     : https://prove2.me/submissions/33184ba2-292e-4bd2-a666-2676e31cea4e

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_Walk

set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution (c : Pt) (s : Side) : lat1 c s = sideEdge c (latA s) := by cases s <;> rfl
end ULHC
