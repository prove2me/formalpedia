-- Prove2me | solution 1 for PI.ComplexConjugateDerivative.gN_eq_frob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:34:23.623714+00:00
-- url     : https://prove2.me/submissions/ba7ade84-6c28-414e-bba0-fb0da7e6b5e4

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
open scoped Matrix.Norms.Frobenius
namespace PI.ComplexConjugateDerivative
theorem _root_.solution (g : B.Mat k r) : B.gN g = ‖g‖ := by
  rw [Matrix.frobenius_norm_def]
  unfold B.gN
  rw [Real.sqrt_eq_rpow]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.normSq_eq_norm_sq, Real.rpow_two]
end PI.ComplexConjugateDerivative
