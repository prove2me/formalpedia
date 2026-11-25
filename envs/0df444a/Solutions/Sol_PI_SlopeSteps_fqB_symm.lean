-- Prove2me | solution 1 for PI.SlopeSteps.fqB_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:27:52.469023+00:00
-- url     : https://prove2.me/submissions/ef693042-3e33-4c77-b59a-2f5c3df7b19c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_NablaBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_GramMatrixDuality
import Theorems.Thm_PI_SlopeSteps_fqB_apply

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
variable {σ : Type}
namespace PI.SlopeSteps
theorem _root_.solution (c : ℚ) (P Q : MvPolynomial σ ℚ) : fqB c P Q = fqB c Q P := by
  rw [fqB_apply, fqB_apply, we_fock_symm]
end PI.SlopeSteps
