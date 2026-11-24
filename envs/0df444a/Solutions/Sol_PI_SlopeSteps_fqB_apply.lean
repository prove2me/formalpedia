-- Prove2me | solution 1 for PI.SlopeSteps.fqB_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:33:14.66261+00:00
-- url     : https://prove2.me/submissions/480e2c5b-d92d-427f-ad36-7d6ecfe95c88

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_NablaBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_GramMatrixDuality

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
theorem _root_.solution (c : ℚ) (P Q : MvPolynomial σ ℚ) : fqB c P Q = fockQ P Q / c := rfl
end PI.SlopeSteps
