-- Prove2me | solution 1 for PI.PC.lcmUpto_le_three_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:03:15.841372+00:00
-- url     : https://prove2.me/submissions/52bffa3d-4868-4807-9ef2-d1bf7cad1348

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PrimeCountBoundOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PsiUpperBoundOfLtThirtyMulSixPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.PC
open Real
namespace PI.PC
theorem _root_.solution : ∀ n < 30, Nat.lcmUpto n ≤ 3 ^ n := by
  decide +kernel
end PI.PC
