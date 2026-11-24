-- Prove2me | solution 1 for PI.PolynomialProperness.GN.inv_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:36:43.369426+00:00
-- url     : https://prove2.me/submissions/9cf2f5eb-7db8-48ef-bde7-1eacfeef27ab

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
theorem _root_.solution {k r : ℕ} {g : B.Mat k r} (hg : g ∈ B.GV k r) : g⁻¹ ∈ B.GV k r :=
  ((unitary_group_holds _ _ (hpk_isUnit_det k r)).2.2 g hg).2
end PI.PolynomialProperness.GN
