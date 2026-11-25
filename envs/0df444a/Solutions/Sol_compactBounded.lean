-- Prove2me | solution 1 for compactBounded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:04:00.92713+00:00
-- url     : https://prove2.me/submissions/0c6d5f44-e2dd-4b62-ad49-bc2421b53732

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AdCpctDen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdicCompactDensity_ExistsNatLocal
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_AdCpctDen
import Theorems.Thm_PI_adCpctDen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.AdCpctDen := PI.adCpctDen
