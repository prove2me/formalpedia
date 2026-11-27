-- Prove2me | solution 1 for PI.VolStabSW.compG_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:21:33.947865+00:00
-- url     : https://prove2.me/submissions/18844931-1cb6-4016-8c81-c288d429a7f2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_PullLocSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FinTheta
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_EventuallyStruct
import Theorems.Thm_PI_VolStabSW_CompGAux_compG_gen

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
theorem _root_.solution : CompG := by
  unfold CompG InCtx
  first
  | (intros; apply CompGAux.compG_gen)
  | (intro F E _ _ _ _ _ _ σ M J a _ _ g; exact CompGAux.compG_gen σ J a g)
end PI.VolStabSW
