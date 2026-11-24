-- Prove2me | solution 1 for ValueAwareRR.trueOptimal_reversed_filtered
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T09:07:02.080081+00:00
-- url     : https://prove2.me/submissions/e3c1b766-e3ad-4083-b37f-80cd6e43a09d

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
import Theorems.Thm_ValueAwareRR_filteredSum_signReverse
import Theorems.Thm_ValueAwareRR_trueOptimal_filtered

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution (m : ℚ) :
    filteredSum m (signReverse trueOptimalOrder) = -10 / 9 := by
  rw [filteredSum_signReverse, trueOptimal_filtered]
  ring
end ValueAwareRR
