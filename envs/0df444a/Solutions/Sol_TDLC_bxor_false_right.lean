-- Prove2me | solution 1 for TDLC.bxor_false_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:24:15.161521+00:00
-- url     : https://prove2.me/submissions/749d1934-e50e-404a-b0f6-b55b8182adbd


import Definitions.Def_TDLC_Solution

set_option autoImplicit true
open TDLC
universe u
namespace TDLC
theorem _root_.solution (b : Bool) : bxor b false = b := by
  cases b <;> rfl
end TDLC
