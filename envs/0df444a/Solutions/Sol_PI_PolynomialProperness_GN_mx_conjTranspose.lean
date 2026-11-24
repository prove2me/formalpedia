-- Prove2me | solution 1 for PI.PolynomialProperness.GN.mx_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:51:05.384304+00:00
-- url     : https://prove2.me/submissions/9e916765-8e2b-4975-aa72-60deec0396b4

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_ZhatNormLinearBound
import Theorems.Thm_PI_PolynomialProperness_GN_mx_nonneg
import Theorems.Thm_PI_PolynomialProperness_GN_entry_le_mx
import Theorems.Thm_PI_PolynomialProperness_GN_mx_le_iff

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
theorem _root_.solution {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) : C2.mx Mᴴ = C2.mx M := by
  apply le_antisymm
  · refine (mx_le_iff _ (mx_nonneg M)).2 fun i j => ?_
    rw [conjTranspose_apply, norm_star]; exact entry_le_mx M j i
  · refine (mx_le_iff _ (mx_nonneg Mᴴ)).2 fun i j => ?_
    have := entry_le_mx Mᴴ j i
    rwa [conjTranspose_apply, norm_star] at this
end PI.PolynomialProperness.GN
