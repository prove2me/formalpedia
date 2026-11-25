-- Prove2me | solution 1 for PI.PolynomialProperness.CB.det_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:22:40.621173+00:00
-- url     : https://prove2.me/submissions/c82ae86a-be12-4523-99f9-3e2e01172e58

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
theorem _root_.solution {m : ℕ} {L : Matrix (Fin m) (Fin m) ℂ} (hL : L ∈ LTset m) : L.det = 1 := by
  have h : L.IsLowerTriangular := fun a b hab => hL.1 _ _ hab
  rw [det_of_isLowerTriangular _ h]
  exact Finset.prod_eq_one fun t _ => hL.2 t
end PI.PolynomialProperness.CB
