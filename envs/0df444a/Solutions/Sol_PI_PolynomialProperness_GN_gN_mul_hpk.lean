-- Prove2me | solution 1 for PI.PolynomialProperness.GN.gN_mul_hpk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:38:38.511477+00:00
-- url     : https://prove2.me/submissions/3a52e0ed-e467-4fa1-bb66-5a0aa7a4e868

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_ZhatNormLinearBound
import Theorems.Thm_PI_PolynomialProperness_GN_hpk_herm
import Theorems.Thm_PI_PolynomialProperness_GN_gN_conjTranspose
import Theorems.Thm_PI_PolynomialProperness_GN_gN_hpk_mul

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
theorem _root_.solution {k r : ℕ} (g : B.Mat k r) : B.gN (g * Hpk k r) = B.gN g := by
  have e : g * Hpk k r = (Hpk k r * gᴴ)ᴴ := by
    rw [conjTranspose_mul, hpk_herm, conjTranspose_conjTranspose]
  rw [e, gN_conjTranspose, gN_hpk_mul, gN_conjTranspose]
end PI.PolynomialProperness.GN
