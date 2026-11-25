-- Prove2me | solution 1 for PI.PolynomialProperness.GN.gN_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:28:30.563816+00:00
-- url     : https://prove2.me/submissions/a32365d8-df91-4f19-b763-3383f6d1214b

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_ZhatNormLinearBound
import Theorems.Thm_PI_PolynomialProperness_GN_gN_eq
import Theorems.Thm_PI_PolynomialProperness_GN_hs_conjTranspose

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
theorem _root_.solution {k r : ℕ} (g : B.Mat k r) : B.gN gᴴ = B.gN g := by
  rw [gN_eq, gN_eq, hs_conjTranspose]
end PI.PolynomialProperness.GN
