-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.GelfCpt.gelfCpt_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:10:46.99067+00:00
-- url     : https://prove2.me/submissions/bcd0aa7c-b705-4bb0-854e-741933acf627

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGelfandAverage_AvgStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGelfandAverage_GelfCptOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGelfandAverage_MulIntMatMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGelfandAverage_IntegrableOfContinuousCpt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGelfandAverage_GelfCptOf
import Theorems.Thm_PI_UnitaryGroupMassFormula_GelfCpt_avgStep
import Theorems.Thm_PI_UnitaryGroupMassFormula_GelfCpt_gelfCpt_of_steps
import Theorems.Thm_PI_UnitaryGroupMassFormula_GelfCpt_mulStep


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.GelfCpt
namespace PI.UnitaryGroupMassFormula.GelfCpt
theorem _root_.solution : PI.UMultOne.IntSpan → PI.UMultOne.ConvComm → PI.UMultOne.GelfandCompact :=
  gelfCpt_of_steps avgStep mulStep
end PI.UnitaryGroupMassFormula.GelfCpt
