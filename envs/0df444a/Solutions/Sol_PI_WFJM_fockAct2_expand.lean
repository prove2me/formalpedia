-- Prove2me | solution 1 for PI.WFJM.fockAct2_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:05:36.730708+00:00
-- url     : https://prove2.me/submissions/d6c0cb00-45cf-4514-85c2-f2f17c324881

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Theorems.Thm_PI_WFJM_fockAct2_eq
import Theorems.Thm_PI_WFJM_fockAct2_Eab

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
namespace PI.WFJM
theorem _root_.solution (Y : Mat r s) :
    fockAct2 p q r s Y = ∑ c, ∑ d, Y c d • fockAct2 p q r s (Eab c d) := by
  rw [fockAct2_eq]
  simp only [fockAct2_Eab, Finset.smul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_comm
end PI.WFJM
