-- Prove2me | solution 1 for TDLC.bxor_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:24:34.946796+00:00
-- url     : https://prove2.me/submissions/a4f2ac54-1dab-4067-8c87-078524fc31e0


import Definitions.Def_TDLC_Solution

set_option autoImplicit true
open TDLC
universe u
namespace TDLC
theorem _root_.solution (a b : Bool) : bxor a b = bxor b a := by
  cases a <;> cases b <;> rfl
end TDLC
