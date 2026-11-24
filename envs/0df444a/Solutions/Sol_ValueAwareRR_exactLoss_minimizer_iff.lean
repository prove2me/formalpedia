-- Prove2me | solution 1 for ValueAwareRR.exactLoss_minimizer_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T09:08:58.998874+00:00
-- url     : https://prove2.me/submissions/6dd078d2-0700-410e-a771-630b9d94a2df

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution (m : ℚ) (hm : 2 ≤ m) (o : SignedOrder) :
    exactLoss m o = exactLoss m trueOptimalOrder ↔
      o = trueOptimalOrder ∨ o = signReverse trueOptimalOrder := by
  rcases o with ⟨r, s⟩
  cases r <;> cases s <;>
    simp [exactLoss, terminalLossFromFiltered, filteredSum, prefixOne,
      prefixTwo, prefixThree, orderedResidual, residual, orderAt,
      representativeOrder, negateLabel, contraction, stepSize, familyA, familyB,
      trueOptimalOrder, signReverse] <;>
    ring_nf <;> nlinarith
end ValueAwareRR
