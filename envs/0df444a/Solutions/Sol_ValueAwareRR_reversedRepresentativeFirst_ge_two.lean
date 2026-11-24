-- Prove2me | solution 1 for ValueAwareRR.reversedRepresentativeFirst_ge_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T09:04:44.394098+00:00
-- url     : https://prove2.me/submissions/858f9c11-d107-4ec4-92e6-624499be6ae3

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution (r : Representative) :
    2 ≤ (negateLabel (representativeOrder r 0)).val := by
  cases r <;> decide
end ValueAwareRR
