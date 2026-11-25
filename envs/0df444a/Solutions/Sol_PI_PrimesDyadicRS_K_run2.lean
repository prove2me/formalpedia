-- Prove2me | solution 1 for PI.PrimesDyadicRS.K.run2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:04:47.255045+00:00
-- url     : https://prove2.me/submissions/e3754ce3-f597-4348-9420-d8b85866412d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_SmallLoop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_Run2

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
theorem _root_.solution : run 65536 3030 32768 32768 1612 = true := by decide +kernel
end PI.PrimesDyadicRS.K
