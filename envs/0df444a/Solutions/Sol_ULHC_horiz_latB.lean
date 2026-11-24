-- Prove2me | solution 1 for ULHC.horiz_latB
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:48:21.304081+00:00
-- url     : https://prove2.me/submissions/ab32290f-e806-42ad-8d60-5d0af087ee1b

import Definitions.Def_ULHC_Phase
import Definitions.Def_ULHC_Phase2

set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution (s : Side) : (latB s).horiz = !s.horiz := by cases s <;> rfl
end ULHC
