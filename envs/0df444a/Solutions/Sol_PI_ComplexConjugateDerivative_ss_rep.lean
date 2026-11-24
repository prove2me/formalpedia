-- Prove2me | solution 1 for PI.ComplexConjugateDerivative.ss_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:42:22.413956+00:00
-- url     : https://prove2.me/submissions/5a65ae68-8f52-487a-90a3-51e4276c0d27

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
theorem _root_.solution {f : B.Mat k r → E} (hf : SS k r f) {g : B.Mat k r} (hg : g ∈ B.GV k r) :
    ∃ (U : Set (B.Mat k r)) (f' : B.Mat k r → E), IsOpen U ∧ g ∈ U ∧ DifferentiableAt ℝ f' g ∧
      ∀ h ∈ U, h ∈ B.GV k r → f h = f' h := by
  obtain ⟨U, f', hU, hgU, hcd, hfe⟩ := hf g hg
  exact ⟨U, f', hU, hgU, (hcd.contDiffAt (hU.mem_nhds hgU)).differentiableAt (by simp), hfe⟩
end PI.ComplexConjugateDerivative
