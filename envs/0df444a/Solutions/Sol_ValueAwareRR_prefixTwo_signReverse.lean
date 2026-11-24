-- Prove2me | solution 1 for ValueAwareRR.prefixTwo_signReverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:56:52.305417+00:00
-- url     : https://prove2.me/submissions/3344f9a1-3196-4375-a688-369963195d7c

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
import Theorems.Thm_ValueAwareRR_orderedResidual_signReverse

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution (m : ℚ) (o : SignedOrder) :
    prefixTwo m (signReverse o) = -prefixTwo m o := by
  simp only [prefixTwo, orderedResidual_signReverse]
  ring
end ValueAwareRR
