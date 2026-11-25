-- Prove2me | solution 1 for PI.JetsPhW.W.pderiv_subst_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:14:39.458111+00:00
-- url     : https://prove2.me/submissions/cc1a8dd5-59a5-4aa7-a354-c8950e28c464

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_TwoUnit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_ExpLog
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_CoeffPowEqZeroOfDegreeLt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_ChainSt
import Theorems.Thm_PI_JetsPhW_Ch_pderiv_subst_X_self


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.JetsPhW PI.JetsPhW.W
open PI.JetsPhW
namespace PI.JetsPhW.W
theorem _root_.solution : PdSelf := fun _ _ _ i g => Ch.pderiv_subst_X_self i g
end PI.JetsPhW.W
