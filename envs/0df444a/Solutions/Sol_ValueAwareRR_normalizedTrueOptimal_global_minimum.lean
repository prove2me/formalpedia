-- Prove2me | solution 1 for ValueAwareRR.normalizedTrueOptimal_global_minimum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T09:15:04.157359+00:00
-- url     : https://prove2.me/submissions/86504764-ecb0-4d49-a918-121cdaf54573

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
import Theorems.Thm_ValueAwareRR_trueOptimalOrder_global_minimum
import Theorems.Thm_ValueAwareRR_normalizedExactLoss_scaling

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution
    (m : ℚ) (hm : 2 ≤ m) (o : SignedOrder) :
    normalizedExactLoss m trueOptimalOrder ≤ normalizedExactLoss m o := by
  rw [normalizedExactLoss_scaling, normalizedExactLoss_scaling]
  exact mul_le_mul_of_nonneg_left (trueOptimalOrder_global_minimum m hm o) (sq_nonneg _)
end ValueAwareRR
