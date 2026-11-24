-- Prove2me | solution 1 for ULHC.horiz_opp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:18:43.817872+00:00
-- url     : https://prove2.me/submissions/dd6124a9-de46-4970-9e5c-4ae0f255c418

import Definitions.Def_ULHC_Phase
import Definitions.Def_ULHC_Phase2

set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution (s : Side) : s.opp.horiz = s.horiz := by cases s <;> rfl
end ULHC
