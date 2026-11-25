-- Prove2me | solution 1 for PI.FJMX.shapeProd_der
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:38:52.170904+00:00
-- url     : https://prove2.me/submissions/202594eb-cb11-4504-9225-a888f9c73a9e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistHW
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
open MvPolynomial FockH1Action PI.FJM
noncomputable section
open PI PI.FJMX
variable {p q r s : ℕ}
variable {m k : ℕ}
namespace PI.FJMX
theorem _root_.solution (D : Derivation ℂ (Pol p q r s) (Pol p q r s))
    (M : Matrix (Fin m) (Fin k) (Pol p q r s)) (α : List ℕ) (h : ∀ t, D (leadT M t) = 0) :
    D (shapeProd M α) = 0 := by
  unfold shapeProd
  apply deriv_prod_eq_zero
  intro t _
  exact deriv_pow_eq_zero _ _ _ (h _)
end PI.FJMX
