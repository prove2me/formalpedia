-- Prove2me | solution 1 for PI.FJM.leftDiagonalActionFormula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:32:33.331751+00:00
-- url     : https://prove2.me/submissions/ef67db3f-e5f3-4f8e-84e0-34722cbf9a4c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Theorems.Thm_PI_WFJM_leftDiagonalActionFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action
open PI PI.FJM
namespace PI.FJM
theorem _root_.solution : FormWt1 := by
  exact PI.WFJM.leftDiagonalActionFormula
end PI.FJM
