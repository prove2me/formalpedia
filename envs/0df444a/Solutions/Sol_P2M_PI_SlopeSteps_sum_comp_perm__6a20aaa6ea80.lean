-- Prove2me | solution 1 for P2M_PI_SlopeSteps_sum_comp_perm__6a20aaa6ea80
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:13:15.327856+00:00
-- url     : https://prove2.me/submissions/94acdac9-94a5-42f8-acb2-956bd7564060

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
theorem _root_.solution {M : Type*} [AddCommMonoid M] {k : ℕ} {n : Type*} [Fintype n] [DecidableEq n]
    (F : (Fin k → n) → M) (τ : Equiv.Perm (Fin k)) : ∑ f : Fin k → n, F (fun i => f (τ i)) = ∑ f, F f :=
  Equiv.sum_comp (Equiv.arrowCongr τ.symm (Equiv.refl n)) F
end PI.SlopeSteps
