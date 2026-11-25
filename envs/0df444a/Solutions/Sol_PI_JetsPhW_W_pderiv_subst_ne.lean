-- Prove2me | solution 1 for PI.JetsPhW.W.pderiv_subst_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:09:47.2698+00:00
-- url     : https://prove2.me/submissions/56964c5a-3642-46b0-acb9-de2d931a9cb6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_TwoUnit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_ExpLog
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_CoeffPowEqZeroOfDegreeLt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_ChainSt
import Theorems.Thm_PI_JetsPhW_Ch_pderiv_subst_X_ne


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
theorem _root_.solution : PdNe := fun _ _ _ _ _ g h => Ch.pderiv_subst_X_ne h g
end PI.JetsPhW.W
