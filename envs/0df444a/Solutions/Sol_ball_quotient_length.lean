-- Prove2me | solution 1 for ball_quotient_length
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:08:58.826867+00:00
-- url     : https://prove2.me/submissions/d2659394-a6e5-4fee-95d7-f4210f1487f1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BallQuotLen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BallQuotientLength_LengthBallQuotientEqSumMulFdeg
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_BallQuotLen
import Theorems.Thm_PI_UnitaryGroupMassFormula_BallQuotLen_ballQuotLen_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.BallQuotLen := PI.UnitaryGroupMassFormula.BallQuotLen.ballQuotLen_main
