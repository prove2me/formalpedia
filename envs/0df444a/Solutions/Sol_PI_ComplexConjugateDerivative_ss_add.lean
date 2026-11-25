-- Prove2me | solution 1 for PI.ComplexConjugateDerivative.ss_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:37:32.499816+00:00
-- url     : https://prove2.me/submissions/e0a7900d-5c88-4de4-b0ee-6e29523b34ee

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSecondOrder_HasDerivAtDOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open PI PI.ComplexConjugateDerivative
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt
variable {k r : ℕ}
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace PI.ComplexConjugateDerivative
theorem _root_.solution {f₁ f₂ : B.Mat k r → E} (h₁ : SS k r f₁) (h₂ : SS k r f₂) : SS k r (f₁ + f₂) := by
  intro g₀ hg₀
  obtain ⟨U₁, f₁', hU₁, hg₁, hc₁, he₁⟩ := h₁ g₀ hg₀
  obtain ⟨U₂, f₂', hU₂, hg₂, hc₂, he₂⟩ := h₂ g₀ hg₀
  refine ⟨U₁ ∩ U₂, fun h => f₁' h + f₂' h, hU₁.inter hU₂, ⟨hg₁, hg₂⟩, ?_, ?_⟩
  · exact (hc₁.mono Set.inter_subset_left).add (hc₂.mono Set.inter_subset_right)
  · intro g hg hG
    simp only [Pi.add_apply, he₁ g hg.1 hG, he₂ g hg.2 hG]
end PI.ComplexConjugateDerivative
