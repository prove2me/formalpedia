-- Prove2me | solution 1 for bessel_levi_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:10:50.566726+00:00
-- url     : https://prove2.me/submissions/0a2419ad-d908-4301-8c71-fba1184d9e29

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselLeviAction_MulVecBvecApply
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_BesselLevi
import Theorems.Thm_PI_UnitaryGroupMassFormula_BesselLevi_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.BesselLevi.BesselLevi :=
  PI.UnitaryGroupMassFormula.BesselLevi.main
