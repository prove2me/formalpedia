-- Prove2me | solution 1 for cauchy_binet_minors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:42:55.319172+00:00
-- url     : https://prove2.me/submissions/95523343-67f9-448b-be47-cd57243f36de

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WwCauchyBinet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CauchyBinet_WwCauchyBinetMain
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WwCauchyBinet
import Theorems.Thm_PI_WwCauchyBinetWork_wwCauchyBinet_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.WwCauchyBinet.WwCauchyBinet := PI.WwCauchyBinetWork.wwCauchyBinet_main
