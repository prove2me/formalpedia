-- Prove2me | solution 1 for ValueAwareRR.prefixOne_signReverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:56:26.408128+00:00
-- url     : https://prove2.me/submissions/b9093844-becd-49e7-8237-f295177d472c

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
import Theorems.Thm_ValueAwareRR_orderedResidual_signReverse

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution (m : ℚ) (o : SignedOrder) :
    prefixOne m (signReverse o) = -prefixOne m o := by
  simp only [prefixOne, orderedResidual_signReverse]
end ValueAwareRR
