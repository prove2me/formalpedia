-- Prove2me | solution 1 for TDLC.bxor_false_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:24:16.779946+00:00
-- url     : https://prove2.me/submissions/421e69f2-52f0-4fb9-80d5-d148c67fb315


import Definitions.Def_TDLC_Solution

set_option autoImplicit true
open TDLC
universe u
namespace TDLC
theorem _root_.solution (b : Bool) : bxor false b = b := rfl
end TDLC
