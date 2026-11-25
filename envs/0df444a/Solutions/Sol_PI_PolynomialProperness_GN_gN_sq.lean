-- Prove2me | solution 1 for PI.PolynomialProperness.GN.gN_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:33:32.92842+00:00
-- url     : https://prove2.me/submissions/1fad4eca-ec02-4176-a71a-42fbe2d8ebd7

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_ZhatNormLinearBound
import Theorems.Thm_PI_PolynomialProperness_GN_hs_nonneg
import Theorems.Thm_PI_PolynomialProperness_GN_gN_eq

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
theorem _root_.solution {k r : ℕ} (g : B.Mat k r) : B.gN g ^ 2 = hs g := by
  rw [gN_eq, Real.sq_sqrt (hs_nonneg g)]
end PI.PolynomialProperness.GN
