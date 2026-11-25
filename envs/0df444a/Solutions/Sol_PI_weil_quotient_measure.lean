-- Prove2me | solution 1 for PI.weil_quotient_measure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:41:41.69017+00:00
-- url     : https://prove2.me/submissions/61acb564-f67e-4a4e-bb87-142dda62bf5b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WeilQuotMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientMeasure_StepBruhat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientMeasure_InvInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientMeasure_LintegralMulAvgComm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientMeasure_Bruhat
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QuotMeasUniq
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WeilQuotMeas
import Theorems.Thm_PI_WeilQuotMeas_UnitaryGroupMassFormula_stepBruhat
import Theorems.Thm_PI_WeilQuotMeas_UnitaryGroupMassFormula_stepInvInv
import Theorems.Thm_PI_WeilQuotMeas_UnitaryGroupMassFormula_weilQuotient_of_parts
import Theorems.Thm_PI_wqUnique


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI
namespace PI
theorem _root_.solution : PI.WeilQuotMeas.WeilQuotient :=
  PI.WeilQuotMeas.UnitaryGroupMassFormula.weilQuotient_of_parts PI.WeilQuotMeas.UnitaryGroupMassFormula.stepBruhat
    PI.WeilQuotMeas.UnitaryGroupMassFormula.stepInvInv PI.wqUnique
end PI
