-- Prove2me | solution 1 for PI.ComplexConjugateDerivative.bsum_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:41:45.56988+00:00
-- url     : https://prove2.me/submissions/574a39c4-8b12-4341-99df-00e894d2674a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSecondOrder_HasDerivAtDOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSecondOrder_SmoothClassInFiniteOrder

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.ComplexConjugateDerivative
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace PI.ComplexConjugateDerivative
theorem _root_.solution {N : ℕ} (e : Fin N → B.Mat k r) :
    ∀ (ks : List Bool) (Ψ : List (B.Mat k r) → ℝ), (∀ β, 0 ≤ Ψ β) → 0 ≤ bsum e ks Ψ
  | [], _, h => h []
  | _ :: ks, Ψ, h => by
    simp only [bsum]
    exact Finset.sum_nonneg fun i _ => solution e ks _ fun β => h _
end PI.ComplexConjugateDerivative
