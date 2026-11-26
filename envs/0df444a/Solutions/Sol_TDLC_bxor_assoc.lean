-- Prove2me | solution 1 for TDLC.bxor_assoc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:25:13.744744+00:00
-- url     : https://prove2.me/submissions/c7cce9a8-8126-4e78-bc25-803c7790310b


import Definitions.Def_TDLC_Solution

set_option autoImplicit true
open TDLC
universe u
namespace TDLC
theorem _root_.solution (a b c : Bool) : bxor (bxor a b) c = bxor a (bxor b c) := by
  cases a <;> cases b <;> cases c <;> rfl
end TDLC
