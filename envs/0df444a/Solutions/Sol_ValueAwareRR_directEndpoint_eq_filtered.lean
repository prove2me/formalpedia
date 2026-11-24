-- Prove2me | solution 1 for ValueAwareRR.directEndpoint_eq_filtered
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:58:49.492052+00:00
-- url     : https://prove2.me/submissions/db8e21ac-f7b5-443a-92f1-2545df8670b9

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution (m : ℚ) (o : SignedOrder) :
    directEndpoint m o = stepSize ^ 2 * filteredSum m o := by
  rcases o with ⟨r, s⟩
  cases r <;> cases s <;>
    simp [directEndpoint, scalarUpdate, filteredSum, prefixOne, prefixTwo, prefixThree,
      orderedResidual, residual, orderAt, representativeOrder, negateLabel,
      contraction, stepSize, familyA, familyB] <;> ring
end ValueAwareRR
