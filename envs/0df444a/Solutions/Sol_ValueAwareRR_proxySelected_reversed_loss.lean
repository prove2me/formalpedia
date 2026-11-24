-- Prove2me | solution 1 for ValueAwareRR.proxySelected_reversed_loss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T09:15:58.449944+00:00
-- url     : https://prove2.me/submissions/8226288d-b163-47c5-a470-6c0c187cca10

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
import Theorems.Thm_ValueAwareRR_exactLoss_signReverse
import Theorems.Thm_ValueAwareRR_proxySelected_loss

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution (m : ℚ) :
    exactLoss m (signReverse proxySelectedOrder) =
      2 * (10 * m + 3) ^ 2 / 6561 := by
  rw [exactLoss_signReverse, proxySelected_loss]
end ValueAwareRR
