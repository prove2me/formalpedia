-- Prove2me | solution 1 for PI.PrimesDyadicRS.K.run1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:04:40.349749+00:00
-- url     : https://prove2.me/submissions/3d94c354-78b1-4a18-bc5f-b3c96fb8a46c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_SmallLoop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_Run1

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
theorem _root_.solution : run 32768 1612 32766 2 1 = true := by decide +kernel
end PI.PrimesDyadicRS.K
