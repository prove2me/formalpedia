-- Prove2me | solution 1 for ValueAwareRR.representativeFirst_lt_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T09:04:38.630647+00:00
-- url     : https://prove2.me/submissions/01b10598-6629-4fdc-a677-421617a224ec

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution (r : Representative) :
    (representativeOrder r 0).val < 2 := by
  cases r <;> decide
end ValueAwareRR
