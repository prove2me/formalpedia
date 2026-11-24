-- Prove2me | solution 1 for ValueAwareRR.proxySelected_loss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:59:07.31398+00:00
-- url     : https://prove2.me/submissions/5227c33c-97e9-4204-b835-41852220a6ca

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
import Theorems.Thm_ValueAwareRR_proxySelected_filtered

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution (m : ℚ) :
    exactLoss m proxySelectedOrder = 2 * (10 * m + 3) ^ 2 / 6561 := by
  rw [exactLoss, proxySelected_filtered]
  norm_num [terminalLossFromFiltered, stepSize]
  ring
end ValueAwareRR
