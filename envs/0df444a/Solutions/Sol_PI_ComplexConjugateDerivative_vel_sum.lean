-- Prove2me | solution 1 for PI.ComplexConjugateDerivative.vel_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:38:42.85903+00:00
-- url     : https://prove2.me/submissions/eabdcf36-7806-4f4d-9990-35a63a6b74c1

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
theorem _root_.solution (b : Bool) {N : ℕ} (c : Fin N → ℝ) (e : Fin N → B.Mat k r) (g : B.Mat k r) :
    vel b (∑ i, c i • e i) g = ∑ i, c i • vel b (e i) g := by
  cases b with
  | true =>
    simp only [vel, Finset.sum_mul, smul_mul_assoc, ← Finset.sum_neg_distrib, smul_neg]
  | false =>
    simp only [vel, Finset.mul_sum, mul_smul_comm]
end PI.ComplexConjugateDerivative
