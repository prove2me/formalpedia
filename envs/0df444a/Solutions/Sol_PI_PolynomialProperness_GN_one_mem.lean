-- Prove2me | solution 1 for PI.PolynomialProperness.GN.one_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:39:31.265503+00:00
-- url     : https://prove2.me/submissions/ddf84498-2756-4d3e-a043-afca0cfd8235

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_ZhatNormLinearBound
import Theorems.Thm_PI_PolynomialProperness_GN_hpk_isUnit_det
import Theorems.Thm_Formalism_QuantumDeterminants_unitary_group_holds


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
theorem _root_.solution (k r : ℕ) : (1 : B.Mat k r) ∈ B.GV k r :=
  (unitary_group_holds _ _ (hpk_isUnit_det k r)).1
end PI.PolynomialProperness.GN
