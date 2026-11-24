-- Prove2me | solution 1 for ULHC.horiz_latA
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:48:18.536776+00:00
-- url     : https://prove2.me/submissions/74a9e8e9-d373-475e-924a-e7097f0601af

import Definitions.Def_ULHC_Phase
import Definitions.Def_ULHC_Phase2

set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution (s : Side) : (latA s).horiz = !s.horiz := by cases s <;> rfl
end ULHC
