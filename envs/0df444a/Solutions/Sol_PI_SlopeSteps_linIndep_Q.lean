-- Prove2me | solution 1 for PI.SlopeSteps.linIndep_Q
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:59:20.345048+00:00
-- url     : https://prove2.me/submissions/0ac276f2-a479-4784-9efc-66f7cab6d769

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_NablaBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_GramMatrixDuality
import Theorems.Thm_PI_SlopeSteps_intQ_injective

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
theorem _root_.solution {N r : ℕ} {M : Submodule ℤ (MvPolynomial (Fin N × Fin N) ℤ)} (e : Module.Basis (Fin r) ℤ M) :
    LinearIndependent ℚ (fun i => intQ N N (e i : MvPolynomial (Fin N × Fin N) ℤ)) := by
  have h1 : LinearIndependent ℤ (fun i => intQ N N (e i : MvPolynomial (Fin N × Fin N) ℤ)) :=
    e.linearIndependent.map' ((intQ N N).comp M.subtype) (by
      rw [LinearMap.ker_eq_bot]; exact (intQ_injective N).comp M.injective_subtype)
  exact (LinearIndependent.iff_fractionRing ℤ ℚ).mp h1
end PI.SlopeSteps
