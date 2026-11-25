-- Prove2me | solution 1 for P2M_PI_FJMX_shapeProd_der__29b51981dd02
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:44:39.87727+00:00
-- url     : https://prove2.me/submissions/eba6840d-f2d0-404d-9cfb-0251246e85d1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurElim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistWt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LeadTDerCols
import Theorems.Thm_PI_FJMX_deriv_pow_eq_zero
import Theorems.Thm_PI_FJMX_deriv_prod_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PI PI.FJMX
variable {A : Type*} [CommRing A] [Algebra ℂ A] {m k : ℕ}
namespace PI.FJMX
theorem _root_.solution (D : Derivation ℂ A A) (M : Matrix (Fin m) (Fin k) A) (α : List ℕ)
    (h : ∀ t, D (PI.FJM.leadT M t) = 0) : D (PI.FJM.shapeProd M α) = 0 := by
  unfold PI.FJM.shapeProd
  apply deriv_prod_eq_zero
  intro t _
  exact deriv_pow_eq_zero _ _ _ (h _)
end PI.FJMX
