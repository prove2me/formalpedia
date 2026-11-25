-- Prove2me | solution 1 for P2M_discrNe__3cb89ad740ba
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:01:39.793873+00:00
-- url     : https://prove2.me/submissions/fa59c71e-121e-4cf5-953e-cd63af3d2536

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DiscrNe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NonzeroDiscriminants_DiscMain
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_DiscrNe
import Theorems.Thm_DiscrNeWork_discrNe_all


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.DiscrNe := DiscrNeWork.discrNe_all
