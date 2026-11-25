-- Prove2me | solution 1 for PI.WFJM.minusPart_raise
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:05:39.526502+00:00
-- url     : https://prove2.me/submissions/44ed725a-c8a5-4773-8dde-9e12365cee61

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Theorems.Thm_PI_WFJM_minusPart_eq_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action
open PI PI.WFJM
open MvPolynomial
open PI.FJM
open MvPolynomial
variable {σ : Type*}
namespace PI.WFJM
theorem _root_.solution (A : Module.End ℂ (MvPolynomial σ ℂ))
    (hA : ∀ (d : ℕ) (Q : MvPolynomial σ ℂ), Q ∈ homog σ d → A Q ∈ homog σ (d + 2))
    (P : MvPolynomial σ ℂ) : minusPart A P = 0 := by
  rw [minusPart_eq_sum]
  refine Finset.sum_eq_zero fun d _ => ?_
  rw [homogeneousComponent_of_mem (hA (d + 2) _ (homogeneousComponent_mem (d + 2) P)),
    if_neg (by omega)]
end PI.WFJM
