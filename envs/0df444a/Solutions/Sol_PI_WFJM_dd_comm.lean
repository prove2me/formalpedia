-- Prove2me | solution 1 for PI.WFJM.dd_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:19:30.680933+00:00
-- url     : https://prove2.me/submissions/941aee6a-38f5-454c-b531-f50c2a4e5e35

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Theorems.Thm_PI_WFJM_pderiv_comm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix FockH1Action
namespace PI.WFJM
end PI.WFJM
namespace PI.WFJM
open MvPolynomial
private theorem pderiv_toLinearMap_apply {σ : Type*} (i : σ) (P : MvPolynomial σ ℂ) :
    (pderiv i).toLinearMap P = pderiv i P := rfl
private theorem moduleEnd_mul_apply {M : Type*} [AddCommGroup M] [Module ℂ M]
    (f g : Module.End ℂ M) (x : M) : (f * g) x = f (g x) := rfl
open PI.FJM
section Grade
open MvPolynomial
variable {σ : Type*}
end Grade
section Lap
variable {p q r s : ℕ}
end Lap
section HW
variable {p q r s : ℕ}
open MvPolynomial
end HW
end PI.WFJM
namespace PI.FJM
end PI.FJM
end
end

set_option autoImplicit false
noncomputable section
open Matrix FockH1Action
open PI PI.WFJM
open MvPolynomial
open PI.FJM
namespace PI.WFJM
theorem _root_.solution {p q r s : ℕ} (l l' : Ln p q r s) : dd l l' = dd l' l := by
  apply LinearMap.ext
  intro P
  simp only [PI.FJM.dd, moduleEnd_mul_apply, pderiv_toLinearMap_apply]
  exact pderiv_comm l l' P
end PI.WFJM
