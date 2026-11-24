-- Prove2me | solution 1 for ULHC.latA_opp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:33:38.269697+00:00
-- url     : https://prove2.me/submissions/52b0dfaa-715d-45d5-b793-503f793a2b35

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_Walk

set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution (s : Side) : latA s.opp = latA s := by cases s <;> rfl
end ULHC
