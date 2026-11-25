-- Prove2me | solution 1 for PI.ComplexConjugateDerivative.inLie_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:34:33.806419+00:00
-- url     : https://prove2.me/submissions/9afa8960-aee8-4951-8004-545fba47f40f

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
namespace PI.ComplexConjugateDerivative
theorem _root_.solution {X : B.Mat k r} (hX : B.inLie k r X) : B.inLie k r (-X) := by
  unfold B.inLie at *
  rw [Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, ← neg_add, hX, neg_zero]
end PI.ComplexConjugateDerivative
