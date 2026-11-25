-- Prove2me | solution 1 for adelic_compact_real_places
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:08:55.169484+00:00
-- url     : https://prove2.me/submissions/ebc57935-f9dc-48cb-a705-d63821a74ee7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AdBridgeSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RealFieldComparison_JmMulApply
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_BridgeRealK
import Theorems.Thm_PI_UnitaryGroupMassFormula_BridgeRealK_realK


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.AdBridgeSteps.RealK := PI.UnitaryGroupMassFormula.BridgeRealK.realK
