-- Prove2me | solution 1 for ValueAwareRR.exactLoss_signReverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T09:02:21.61633+00:00
-- url     : https://prove2.me/submissions/04a2fa32-4158-418a-a3ff-35fa10417918

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
import Theorems.Thm_ValueAwareRR_filteredSum_signReverse

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution (m : ℚ) (o : SignedOrder) :
    exactLoss m (signReverse o) = exactLoss m o := by
  simp only [exactLoss, filteredSum_signReverse, terminalLossFromFiltered]
  ring
end ValueAwareRR
