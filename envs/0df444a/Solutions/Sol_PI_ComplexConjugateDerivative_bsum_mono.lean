-- Prove2me | solution 1 for PI.ComplexConjugateDerivative.bsum_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:42:33.538729+00:00
-- url     : https://prove2.me/submissions/c71dae17-5664-4950-a9a3-3bd9f4c082d9

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
    ∀ (ks : List Bool) (Ψ₁ Ψ₂ : List (B.Mat k r) → ℝ),
      (∀ β : List (B.Mat k r), β.length = ks.length → (∀ x ∈ β, ∃ i, x = e i) → Ψ₁ β ≤ Ψ₂ β) →
      bsum e ks Ψ₁ ≤ bsum e ks Ψ₂
  | [], _, _, h => h [] rfl (by simp)
  | _ :: ks, Ψ₁, Ψ₂, h => by
    simp only [bsum]
    refine Finset.sum_le_sum fun i _ => solution e ks _ _ fun β hβ hβe => h (e i :: β) (by simp [hβ]) ?_
    intro x hx
    rcases List.mem_cons.1 hx with hx | hx
    · exact ⟨i, hx⟩
    · exact hβe x hx
end PI.ComplexConjugateDerivative
