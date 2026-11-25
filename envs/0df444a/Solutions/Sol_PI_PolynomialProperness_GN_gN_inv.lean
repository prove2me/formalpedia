-- Prove2me | solution 1 for PI.PolynomialProperness.GN.gN_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:06:48.98465+00:00
-- url     : https://prove2.me/submissions/f4cec81a-cc1e-4158-8f2c-fbf775fe31cb

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_ZhatNormLinearBound
import Theorems.Thm_PI_PolynomialProperness_GN_inv_eq
import Theorems.Thm_PI_PolynomialProperness_GN_gN_conjTranspose
import Theorems.Thm_PI_PolynomialProperness_GN_gN_hpk_mul
import Theorems.Thm_PI_PolynomialProperness_GN_gN_mul_hpk

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
namespace PI.PolynomialProperness.GN
theorem _root_.solution {k r : ℕ} {g : B.Mat k r} (hg : g ∈ B.GV k r) : B.gN g⁻¹ = B.gN g := by
  rw [inv_eq hg, gN_mul_hpk, gN_hpk_mul, gN_conjTranspose]
end PI.PolynomialProperness.GN
