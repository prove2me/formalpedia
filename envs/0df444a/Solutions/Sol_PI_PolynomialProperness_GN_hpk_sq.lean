-- Prove2me | solution 1 for PI.PolynomialProperness.GN.hpk_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:55:44.576787+00:00
-- url     : https://prove2.me/submissions/33adebf2-b1d7-43a7-8659-bb5d094da69f

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_ZhatNormLinearBound
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_sq


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
theorem _root_.solution (k r : ℕ) : Hpk k r * Hpk k r = 1 := GBasic.Hpk_sq k r
end PI.PolynomialProperness.GN
