-- Prove2me | solution 1 for PI.ComplexConjugateDerivative.D_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:21:18.232216+00:00
-- url     : https://prove2.me/submissions/3d2bcd32-d4e5-4efe-9370-1f554ed9da46

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
theorem _root_.solution (b : Bool) (X : B.Mat k r) (f : B.Mat k r → E) (g : B.Mat k r) :
    D b X f g = deriv (fun t : ℝ => f (cv b X g t)) 0 := by
  cases b <;> rfl
end PI.ComplexConjugateDerivative
