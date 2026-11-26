-- Prove2me | solution 1 for TDLC.bxor_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:24:15.779354+00:00
-- url     : https://prove2.me/submissions/b2352e23-bdbd-48db-9fe6-ed15749e6230


import Definitions.Def_TDLC_Solution

set_option autoImplicit true
open TDLC
universe u
namespace TDLC
theorem _root_.solution (b : Bool) : bxor b b = false := by
  cases b <;> rfl
end TDLC
