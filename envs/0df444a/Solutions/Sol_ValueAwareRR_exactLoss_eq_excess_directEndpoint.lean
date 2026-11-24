-- Prove2me | solution 1 for ValueAwareRR.exactLoss_eq_excess_directEndpoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T09:13:23.502847+00:00
-- url     : https://prove2.me/submissions/fe99ffc0-601b-422f-9a2b-f8f1a2392da7

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
import Theorems.Thm_ValueAwareRR_directEndpoint_eq_filtered

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution (m : ℚ) (o : SignedOrder) :
    exactLoss m o = excessLoss (directEndpoint m o) := by
  rw [directEndpoint_eq_filtered]
  simp only [exactLoss, terminalLossFromFiltered, excessLoss]
end ValueAwareRR
