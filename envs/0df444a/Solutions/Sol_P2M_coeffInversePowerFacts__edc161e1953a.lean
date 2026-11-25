-- Prove2me | solution 1 for P2M_coeffInversePowerFacts__edc161e1953a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:33:07.381794+00:00
-- url     : https://prove2.me/submissions/eb37f234-15b0-4b7e-b7ce-b43925a08bc2

import Definitions.Def_Formalism_PeriodIntegrals_TayInvPow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TaylorInversePower_SumMultinomialSub
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_TayInvPow
import Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_TayInvPow_main__b5d589cc85a4


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution.{u, v} : PI.TayInvPow.{u, v} := PI.UnitaryGroupMassFormula.TayInvPow.main
