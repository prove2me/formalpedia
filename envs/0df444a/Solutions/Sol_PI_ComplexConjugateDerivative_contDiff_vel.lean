-- Prove2me | solution 1 for PI.ComplexConjugateDerivative.contDiff_vel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:34:07.722228+00:00
-- url     : https://prove2.me/submissions/be239c46-d328-40e4-aafd-b9aaaf7f6fa1

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
theorem _root_.solution (b : Bool) (X : B.Mat k r) {m : WithTop ℕ∞} :
    ContDiff ℝ m (fun h : B.Mat k r => vel b X h) := by
  cases b with
  | true =>
    show ContDiff ℝ m (fun h : B.Mat k r => -(X * h))
    exact (mulL X).contDiff.neg
  | false =>
    show ContDiff ℝ m (fun h : B.Mat k r => h * X)
    exact (mulR X).contDiff
end PI.ComplexConjugateDerivative
