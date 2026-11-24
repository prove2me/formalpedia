-- Prove2me | solution 1 for PI.PolynomialProperness.GN.hpk_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:01:58.513649+00:00
-- url     : https://prove2.me/submissions/d90c30de-3991-43ea-bc79-c5c7d2eecb6f

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_ZhatNormLinearBound
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_herm


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
theorem _root_.solution (k r : ℕ) : (Hpk k r)ᴴ = Hpk k r := GBasic.Hpk_herm k r
end PI.PolynomialProperness.GN
