-- Prove2me | solution 1 for PI.WSF.ci_Alin_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:37:45.075172+00:00
-- url     : https://prove2.me/submissions/060c5afe-9e55-4323-b79b-e6a1327b5474

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_CrRowActRowAct
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_CiEvalMSmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WSF
open MvPolynomial MeasureTheory Matrix
namespace PI.WSF
theorem _root_.solution {N : ℕ} {μ : Measure (Matrix (Fin N) (Fin N) ℂ)} (hμ : IsHaarU N μ)
    (p q : MvPolynomial (Fin N × Fin N) ℂ) : Alin hμ q p = Aform μ p q := rfl
end PI.WSF
