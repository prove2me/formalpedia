-- Prove2me | solution 1 for PI.VolStabW.submDens_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:36:10.639729+00:00
-- url     : https://prove2.me/submissions/c4330abc-62a2-4932-a982-1dbb21b8fc5b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensInfCV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensInfTop
import Theorems.Thm_PI_VolStabW_submLocal_holds
import Theorems.Thm_PI_VolStabW_submDens_of_local


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
theorem _root_.solution : SubmDens := submDens_of_local submLocal_holds
end PI.VolStabW
