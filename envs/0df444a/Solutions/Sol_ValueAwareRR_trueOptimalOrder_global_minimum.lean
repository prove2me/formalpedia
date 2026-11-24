-- Prove2me | solution 1 for ValueAwareRR.trueOptimalOrder_global_minimum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T09:09:08.570115+00:00
-- url     : https://prove2.me/submissions/cb1fd9c7-567c-4378-835b-bd05e6083048

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution (m : ℚ) (hm : 2 ≤ m) (o : SignedOrder) :
    exactLoss m trueOptimalOrder ≤ exactLoss m o := by
  rcases o with ⟨r, s⟩
  cases r <;> cases s <;>
    simp [exactLoss, terminalLossFromFiltered, filteredSum, prefixOne,
      prefixTwo, prefixThree, orderedResidual, residual, orderAt,
      representativeOrder, negateLabel, contraction, stepSize, familyA, familyB,
      trueOptimalOrder] <;>
    ring_nf <;> nlinarith
end ValueAwareRR
