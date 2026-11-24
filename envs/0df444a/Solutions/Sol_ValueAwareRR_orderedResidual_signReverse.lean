-- Prove2me | solution 1 for ValueAwareRR.orderedResidual_signReverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:53:33.482988+00:00
-- url     : https://prove2.me/submissions/8a1be0f6-3ab4-4174-846e-8064d0611aea

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution (m : ℚ) (o : SignedOrder) (k : Fin 4) :
    orderedResidual m (signReverse o) k = -orderedResidual m o k := by
  rcases o with ⟨r, s⟩
  cases r <;> cases s <;> fin_cases k <;>
    simp [orderedResidual, residual, orderAt, representativeOrder, negateLabel,
      signReverse, familyA, familyB]
end ValueAwareRR
