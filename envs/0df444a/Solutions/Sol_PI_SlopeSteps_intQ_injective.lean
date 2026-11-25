-- Prove2me | solution 1 for PI.SlopeSteps.intQ_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:34:13.361715+00:00
-- url     : https://prove2.me/submissions/7d3c6ea5-1074-4adf-8ccc-81ea8aa7a1d2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_NablaBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_GramMatrixDuality
import Theorems.Thm_Formalism_L2_DIV_we_intQ_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.SlopeSteps
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.L2.DIV
namespace PI.SlopeSteps
theorem _root_.solution (N : ℕ) : Function.Injective (intQ N N) := by
  intro p q hpq
  rw [we_intQ_apply, we_intQ_apply] at hpq
  exact map_injective _ (fun a b h => Int.cast_injective h) hpq
end PI.SlopeSteps
