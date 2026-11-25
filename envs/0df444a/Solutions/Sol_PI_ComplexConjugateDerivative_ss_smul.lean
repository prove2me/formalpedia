-- Prove2me | solution 1 for PI.ComplexConjugateDerivative.ss_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:35:06.526842+00:00
-- url     : https://prove2.me/submissions/531918fb-daa7-4b85-a079-8fe52e97c6a1

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
theorem _root_.solution (c : ℝ) {f : B.Mat k r → E} (hf : SS k r f) : SS k r (c • f) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hc, he⟩ := hf g₀ hg₀
  refine ⟨U, fun h => c • f' h, hU, hgU, hc.const_smul c, ?_⟩
  intro g hg hG
  simp only [Pi.smul_apply, he g hg hG]
end PI.ComplexConjugateDerivative
