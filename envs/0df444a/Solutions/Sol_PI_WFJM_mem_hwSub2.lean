-- Prove2me | solution 1 for PI.WFJM.mem_hwSub2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:42:13.23761+00:00
-- url     : https://prove2.me/submissions/231f839e-9293-4f47-8375-35053fbf4275

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Theorems.Thm_PI_WFJM_rightOffDiagonalActionFormula
import Theorems.Thm_PI_WFJM_mem_wtSub2
import Theorems.Thm_PI_WFJM_ne_of_posC

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
variable {p q r s : ℕ}
open MvPolynomial
namespace PI.WFJM
theorem _root_.solution (μ : Ix r s → ℚ) (P : Pol p q r s) :
    P ∈ hwSub (fockAct2 p q r s) μ ↔
      (∀ m ∈ P.support, ∀ c, (wt2 m c : ℚ) + sh2 p q r s c = μ c) ∧
        ∀ c d, posC c d → rai2 (p := p) (q := q) c d P = 0 := by
  rw [FockH1Action.hwSub, Submodule.mem_inf, mem_wtSub2]
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  refine and_congr Iff.rfl (forall_congr' fun c => forall_congr' fun d =>
    forall_congr' fun hcd => ?_)
  rw [rightOffDiagonalActionFormula p q r s c d (ne_of_posC hcd)]
end PI.WFJM
