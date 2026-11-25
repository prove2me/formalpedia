-- Prove2me | solution 1 for PI.VolStabSW.submDens_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:40:34.570053+00:00
-- url     : https://prove2.me/submissions/a1455eb4-8b1f-4016-9df6-034796fc1bdb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensInfCV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensInfTop
import Theorems.Thm_PI_VolStabSW_submLocal_holds
import Theorems.Thm_PI_VolStabSW_submDens_of_local


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
theorem _root_.solution : SubmDens := submDens_of_local submLocal_holds
end PI.VolStabSW
