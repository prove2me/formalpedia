-- Prove2me | solution 1 for PI.PrimesDyadicRS.K.force_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:39:35.004198+00:00
-- url     : https://prove2.me/submissions/fb1ab5a8-9887-49fa-be45-f3ad91a39b75

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_SmallLoop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.PrimesDyadicRS PI.PrimesDyadicRS.K
namespace PI.PrimesDyadicRS.K
theorem _root_.solution (x : Nat) (f : Nat → Bool) : force x f = f x := by
  cases x <;> rfl
end PI.PrimesDyadicRS.K
