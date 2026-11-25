-- Prove2me | solution 1 for PI.TOW.DegW.stepDeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:44:07.006361+00:00
-- url     : https://prove2.me/submissions/393ff3ae-3e9f-417c-ac16-34f8246f653e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_MultidegSingle
import Theorems.Thm_PI_TOW_DegW_step_mem

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
open PI PI.TOW PI.TOW.DegW
open PI.TO PI.TOW
variable {K : Type} [Field K] {n' k : ℕ}
namespace PI.TOW.DegW
theorem _root_.solution : StepDeg := by
  intro K _ n' k d l G hG
  induction l with
  | nil => exact hG
  | cons y l ih =>
    simp only [opWord, List.foldr_cons] at ih ⊢
    exact step_mem y.1 y.2.1 y.2.2 d _ ih
end PI.TOW.DegW
