-- Prove2me | solution 1 for PI.PolynomialProperness.GN.mx_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:55:36.272964+00:00
-- url     : https://prove2.me/submissions/742456ce-42c2-4a4e-8bff-94c14e73e6b9

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_ZhatNormLinearBound

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
theorem _root_.solution {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) : 0 ≤ C2.mx M := norm_nonneg _
end PI.PolynomialProperness.GN
