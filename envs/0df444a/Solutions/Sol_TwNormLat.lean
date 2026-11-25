-- Prove2me | solution 1 for TwNormLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:09:51.069809+00:00
-- url     : https://prove2.me/submissions/76f8cb1c-697e-4ea2-adaa-1432058eea7e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_TwNormLatMain
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_TwNormLat
import Theorems.Thm_PI_TwNormLat_W_twNormLat_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.TwNormLat.TwNormLat := PI.TwNormLat.W.twNormLat_main
