-- Prove2me | solution 1 for P2M_PI_local_global_inclusion__f567540d67ab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:25:33.228135+00:00
-- url     : https://prove2.me/submissions/50959da1-66ed-4cd9-a69f-eeb7ceca0e26

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocGlobIncl
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalGlobalInclusion_SmulMemIdealSmul
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_LocGlobIncl
import Theorems.Thm_PI_LocGlobInclWork_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI
namespace PI
theorem _root_.solution : PI.LocGlobIncl := PI.LocGlobInclWork.main
end PI
