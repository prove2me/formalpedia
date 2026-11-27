-- Prove2me | solution 1 for PI.FJMX.shapeVectorRightHighestWeight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:14:31.128513+00:00
-- url     : https://prove2.me/submissions/432282c2-34dd-4a68-afc1-fc5e7bdb904e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_IsDiagonalBlockIndexRightOfPositiveRoot
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistFin
import Theorems.Thm_PI_FJMX_vecHW2_of
import Theorems.Thm_PI_FJM_rightDiagonalActionFormula
import Theorems.Thm_PI_FJM_rightOffDiagonalActionFormula
import Theorems.Thm_PI_WFJM_rightDiagonalActionFormula
import Theorems.Thm_PI_WFJM_rightOffDiagonalActionFormula


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.FJMX
namespace PI.FJMX
theorem _root_.solution : PI.FJM.VecHW2 := vecHW2_of PI.FJM.rightDiagonalActionFormula PI.FJM.rightOffDiagonalActionFormula
end PI.FJMX
