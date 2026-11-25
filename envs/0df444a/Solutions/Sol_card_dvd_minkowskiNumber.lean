-- Prove2me | solution 1 for card_dvd_minkowskiNumber
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:28:58.378604+00:00
-- url     : https://prove2.me/submissions/0d0d67ec-bdfc-4917-8838-800f22c9d269

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_Minkowski
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_CharpolyDvdOfPowEqOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_PowerSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_MinkowskiBoundOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_Minkowski
import Theorems.Thm_PI_Mk_minkowskiBound_of_steps
import Theorems.Thm_PI_Mk_powerSumStep
import Theorems.Thm_PI_Mk_traceStep


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.MinkowskiBound :=
  PI.Mk.minkowskiBound_of_steps PI.Mk.traceStep PI.Mk.powerSumStep
