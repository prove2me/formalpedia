-- Prove2me | solution 1 for PI.WFJM.mem_hwSub1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:41:46.359801+00:00
-- url     : https://prove2.me/submissions/16631cd8-0c1d-4878-bde9-ba533553fcda

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Theorems.Thm_PI_WFJM_leftOffDiagonalActionFormula
import Theorems.Thm_PI_WFJM_mem_wtSub1
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
theorem _root_.solution (μ : Ix p q → ℚ) (P : Pol p q r s) :
    P ∈ hwSub (fockAct1 p q r s) μ ↔
      (∀ m ∈ P.support, ∀ a, (wt1 m a : ℚ) + sh1 p q r s a = μ a) ∧
        ∀ a b, posC a b → rai1 (r := r) (s := s) a b P = 0 := by
  rw [FockH1Action.hwSub, Submodule.mem_inf, mem_wtSub1]
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  refine and_congr Iff.rfl (forall_congr' fun a => forall_congr' fun b =>
    forall_congr' fun hab => ?_)
  rw [leftOffDiagonalActionFormula p q r s a b (ne_of_posC hab)]
end PI.WFJM
