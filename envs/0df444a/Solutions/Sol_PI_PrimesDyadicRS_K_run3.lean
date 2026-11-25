-- Prove2me | solution 1 for PI.PrimesDyadicRS.K.run3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:04:50.310517+00:00
-- url     : https://prove2.me/submissions/0c007d3d-6fbf-413a-91e6-cb721e05a16a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_SmallLoop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_Run3

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
theorem _root_.solution : run 98304 4388 32768 65536 3030 = true := by decide +kernel
end PI.PrimesDyadicRS.K
