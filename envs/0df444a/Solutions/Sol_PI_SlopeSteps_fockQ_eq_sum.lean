-- Prove2me | solution 1 for PI.SlopeSteps.fockQ_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:22:30.536722+00:00
-- url     : https://prove2.me/submissions/cefd3452-623c-4c52-9e29-39067547b9c1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_MonomialFactorizationLower
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_StdSlopeLowOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_GramMatrixDuality
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_NablaGram

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
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.L2.DIV Matrix
namespace PI.SlopeSteps
theorem _root_.solution {σ : Type} (P Q : MvPolynomial σ ℚ) (S : Finset (σ →₀ ℕ)) (hS : P.support ⊆ S) :
    fockQ P Q = ∑ m ∈ S, P.coeff m * Q.coeff m * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℚ) := by
  unfold fockQ
  refine Finset.sum_subset hS fun m _ hm => ?_
  rw [MvPolynomial.mem_support_iff, not_not] at hm
  rw [hm]
  ring
end PI.SlopeSteps
