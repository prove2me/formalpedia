-- Prove2me | solution 1 for PI.FJM.leftOffDiagonalActionFormula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:43.887397+00:00
-- url     : https://prove2.me/submissions/fafda3b0-07cb-452e-8b44-9b9cc56080ea

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Theorems.Thm_PI_WFJM_leftOffDiagonalActionFormula

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
theorem _root_.solution : FormRaise1 := by
  exact PI.WFJM.leftOffDiagonalActionFormula
end PI.FJM
