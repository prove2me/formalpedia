-- Prove2me | solution 1 for PI.PolynomialProperness.GN.gN_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:03:10.586445+00:00
-- url     : https://prove2.me/submissions/acdc15b5-7243-4dd6-b382-3c8bed1ec849

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_ZhatNormLinearBound
import Theorems.Thm_PI_PolynomialProperness_GN_gN_eq_frob

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open PI PI.PolynomialProperness PI.PolynomialProperness.GN
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt
attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup Matrix.frobeniusNormedAddCommGroup
  Matrix.frobeniusNormedSpace Matrix.frobeniusNormedRing
namespace PI.PolynomialProperness.GN
theorem _root_.solution {k r : ℕ} (a b : B.Mat k r) : B.gN (a * b) ≤ B.gN a * B.gN b := by
  rw [gN_eq_frob, gN_eq_frob, gN_eq_frob]
  exact Matrix.frobenius_norm_mul a b
end PI.PolynomialProperness.GN
