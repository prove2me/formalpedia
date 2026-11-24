-- Prove2me | solution 1 for ULHC.latB_opp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:37:00.857007+00:00
-- url     : https://prove2.me/submissions/15b69454-a516-455a-8608-3a47f567ce76

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_Walk

set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution (s : Side) : latB s.opp = latB s := by cases s <;> rfl
end ULHC
