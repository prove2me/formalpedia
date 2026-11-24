-- Prove2me | solution 1 for ValueAwareRR.residual_sum_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T09:12:43.020865+00:00
-- url     : https://prove2.me/submissions/0aea7941-2546-4d76-8619-c9b440d4cfff

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution (m : ℚ) :
    residual m 0 + residual m 1 + residual m 2 + residual m 3 = 0 := by
  change -familyA m + -familyB m + familyB m + familyA m = 0
  ring
end ValueAwareRR
