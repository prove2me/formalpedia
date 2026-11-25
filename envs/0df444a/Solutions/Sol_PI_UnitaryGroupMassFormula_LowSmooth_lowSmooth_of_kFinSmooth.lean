-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LowSmooth.lowSmooth_of_kFinSmooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:01:12.923237+00:00
-- url     : https://prove2.me/submissions/f3bb7eea-b066-4ee4-885d-eb6330fb770d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_LowCyc
import Definitions.Def_Formalism_PeriodIntegrals_KFinSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerSmoothStability_ExistsFinStableOfMemSSup
import Theorems.Thm_PI_UnitaryGroupMassFormula_LowSmooth_isKFinHpk_of_lowUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LowSmooth
open PI.UpqRep
namespace PI.UnitaryGroupMassFormula.LowSmooth
theorem _root_.solution (hK : PI.KFinSmooth) : PI.LowSmooth := by
  intro k r ε lam H _ _ _ σ w hHC hDS hlow
  exact hK k r ε lam H σ hHC hDS w (isKFinHpk_of_lowUnit hlow)
end PI.UnitaryGroupMassFormula.LowSmooth
