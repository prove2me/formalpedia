-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.ZI.norm_smulRightL_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:48:45.190156+00:00
-- url     : https://prove2.me/submissions/d6ebce46-8b2c-4589-b01c-3e971fd19452

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ZIterA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost PI.UnitaryGroupMassFormula.UsCost.ZI
variable {V I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype I]
namespace PI.UnitaryGroupMassFormula.UsCost.ZI
theorem _root_.solution (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ‖ContinuousLinearMap.smulRightL ℝ V E‖ ≤ 1 := by
  exact ContinuousLinearMap.norm_smulRightL_le
end PI.UnitaryGroupMassFormula.UsCost.ZI
