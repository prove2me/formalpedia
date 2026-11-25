-- Prove2me | solution 1 for PI.PrimesDyadicRS.K.run4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:04:53.57812+00:00
-- url     : https://prove2.me/submissions/c0e00b44-6bed-41b5-890c-194ab9a9c301

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_SmallLoop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_Run4

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
theorem _root_.solution : run 131072 5709 32768 98304 4388 = true := by decide +kernel
end PI.PrimesDyadicRS.K
