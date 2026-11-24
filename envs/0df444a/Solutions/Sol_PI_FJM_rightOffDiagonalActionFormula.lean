-- Prove2me | solution 1 for PI.FJM.rightOffDiagonalActionFormula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:55:48.44982+00:00
-- url     : https://prove2.me/submissions/65dd0389-5c95-405a-863a-3c27efc47db3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Theorems.Thm_PI_WFJM_rightOffDiagonalActionFormula

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
theorem _root_.solution : FormRaise2 := by
  exact PI.WFJM.rightOffDiagonalActionFormula
end PI.FJM
