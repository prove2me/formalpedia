-- Prove2me | solution 1 for additive_integral_generation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:55:58.814134+00:00
-- url     : https://prove2.me/submissions/417a3dad-f072-4492-9ecc-537c07859c9c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AddIntG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_AddIntGTop
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_AddIntG
import Theorems.Thm_PI_AddIntG_Wk_addIntG_top


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.AddIntG.Target := PI.AddIntG.Wk.addIntG_top
