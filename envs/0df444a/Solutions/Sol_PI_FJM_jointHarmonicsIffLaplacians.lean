-- Prove2me | solution 1 for PI.FJM.jointHarmonicsIffLaplacians
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:07:01.439574+00:00
-- url     : https://prove2.me/submissions/c825c6d3-8033-4d05-8b35-c89d872bcd05

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Theorems.Thm_PI_WFJM_jointHarmonicsIffLaplacians

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
theorem _root_.solution : FormJ := by
  exact PI.WFJM.jointHarmonicsIffLaplacians
end PI.FJM
