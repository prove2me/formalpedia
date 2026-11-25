-- Prove2me | solution 1 for PI.PolynomialProperness.CB.det_ut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:04:15.345074+00:00
-- url     : https://prove2.me/submissions/d94f4e8a-baac-4634-9430-69ff16ad959d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_NsqMulVecLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_SecondOrderNormBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt.C2
noncomputable section
open PI PI.PolynomialProperness PI.PolynomialProperness.CB
namespace PI.PolynomialProperness.CB
theorem _root_.solution {m : ℕ} {U : Matrix (Fin m) (Fin m) ℂ} (hU : U ∈ UTset m) : U.det = 1 := by
  have h : U.IsUpperTriangular := fun a b hab => hU.1 _ _ hab
  rw [det_of_isUpperTriangular h]
  exact Finset.prod_eq_one fun t _ => hU.2 t
end PI.PolynomialProperness.CB
