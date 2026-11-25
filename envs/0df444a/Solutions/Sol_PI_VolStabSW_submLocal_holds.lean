-- Prove2me | solution 1 for PI.VolStabSW.submLocal_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:30:22.623267+00:00
-- url     : https://prove2.me/submissions/f5645375-4c8a-4605-b9eb-ff7995bf68a1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensInfCV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensInfTop
import Theorems.Thm_PI_VolStabSW_changeVar_holds
import Theorems.Thm_PI_VolStabSW_linDens_holds
import Theorems.Thm_PI_VolStabSW_submLocal_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
namespace PI.VolStabSW
theorem _root_.solution : SubmLocal := submLocal_of linDens_holds changeVar_holds
end PI.VolStabSW
