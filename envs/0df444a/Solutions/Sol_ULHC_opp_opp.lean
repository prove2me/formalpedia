-- Prove2me | solution 1 for ULHC.opp_opp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:24:26.411787+00:00
-- url     : https://prove2.me/submissions/c529726b-2c19-4223-9259-fb43f9aedf70

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_Walk

set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution (s : Side) : s.opp.opp = s := by cases s <;> rfl
end ULHC
