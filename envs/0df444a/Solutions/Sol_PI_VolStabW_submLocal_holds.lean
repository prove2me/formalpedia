-- Prove2me | solution 1 for PI.VolStabW.submLocal_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:15:41.189824+00:00
-- url     : https://prove2.me/submissions/6e4acc18-d87c-4c1a-9d42-95edd35f40a9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensInfCV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensInfTop
import Theorems.Thm_PI_VolStabW_changeVar_holds
import Theorems.Thm_PI_VolStabW_linDens_holds
import Theorems.Thm_PI_VolStabW_submLocal_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
namespace PI.VolStabW
theorem _root_.solution : SubmLocal := submLocal_of linDens_holds changeVar_holds
end PI.VolStabW
