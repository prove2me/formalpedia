-- Prove2me | solution 1 for PI.FJM.cauchy_highest_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:58:20.339846+00:00
-- url     : https://prove2.me/submissions/ee389912-7c9e-489e-aab0-1574cb3b9e52

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHWOfShape
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauBFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyFin
import Theorems.Thm_PI_FJMB_cauchyHW_of_shape
import Theorems.Thm_PI_FJMX_minorProductDiagonal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.FJM
namespace PI.FJM
theorem _root_.solution : CauchyHW :=
  PI.FJMB.cauchyHW_of_shape PI.FJMX.minorProductDiagonal
end PI.FJM
