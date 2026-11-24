-- Prove2me | solution 1 for ValueAwareRR.exactLoss_eq_filtered_square
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T09:06:07.270016+00:00
-- url     : https://prove2.me/submissions/57e93836-11f3-4149-a6c2-0e316dbe16be

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution (m : ℚ) (o : SignedOrder) :
    exactLoss m o = filteredSum m o ^ 2 / 162 := by
  rw [exactLoss, terminalLossFromFiltered]
  norm_num [stepSize]
  ring
end ValueAwareRR
