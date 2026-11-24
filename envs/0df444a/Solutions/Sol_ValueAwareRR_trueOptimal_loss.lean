-- Prove2me | solution 1 for ValueAwareRR.trueOptimal_loss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:55:58.194801+00:00
-- url     : https://prove2.me/submissions/dffc83a1-d868-40dc-b059-a0a259e56b12

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
import Theorems.Thm_ValueAwareRR_trueOptimal_filtered

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution (m : ℚ) : exactLoss m trueOptimalOrder = 50 / 6561 := by
  rw [exactLoss, trueOptimal_filtered]
  norm_num [terminalLossFromFiltered, stepSize]
end ValueAwareRR
