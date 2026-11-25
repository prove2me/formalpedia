-- Prove2me | solution 1 for PI.TOW.LiftW.stepLift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:56:56.30285+00:00
-- url     : https://prove2.me/submissions/bcd23f3a-4bd3-44df-8d70-ee6905bee48f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_NotMemVarsEmbS
import Theorems.Thm_PI_TOW_LiftW_main_list

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.TOW PI.TOW.LiftW
open PI.TO PI.TOW
variable {K : Type} [CommRing K] {n' k : ℕ}
namespace PI.TOW.LiftW
theorem _root_.solution : StepLift := by
  intro K _ n' k w F
  have h := main_list w F (List.finRange n') (List.nodup_finRange n')
  simpa [concatW, List.mem_finRange] using h
end PI.TOW.LiftW
