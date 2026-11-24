-- Prove2me | solution 1 for PI.ComplexConjugateDerivative.bsum_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:42:34.861556+00:00
-- url     : https://prove2.me/submissions/a090bbce-9bf8-44ee-953c-f1cc2f1efde2

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
theorem _root_.solution {N : ℕ} (e : Fin N → B.Mat k r) (a : ℝ) :
    ∀ (ks : List Bool) (Ψ : List (B.Mat k r) → ℝ), bsum e ks (fun β => a * Ψ β) = a * bsum e ks Ψ
  | [], _ => rfl
  | _ :: ks, Ψ => by
    simp only [bsum]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => solution e a ks _
end PI.ComplexConjugateDerivative
