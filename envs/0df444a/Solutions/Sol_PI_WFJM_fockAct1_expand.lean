-- Prove2me | solution 1 for PI.WFJM.fockAct1_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:05:32.946602+00:00
-- url     : https://prove2.me/submissions/6aacdd1b-0cf2-4761-8c7f-4109c059d787

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Theorems.Thm_PI_WFJM_fockAct1_eq
import Theorems.Thm_PI_WFJM_fockAct1_Eab

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
theorem _root_.solution (X : Mat p q) :
    fockAct1 p q r s X = ∑ a, ∑ b, X a b • fockAct1 p q r s (Eab a b) := by
  rw [fockAct1_eq]
  simp only [fockAct1_Eab, Finset.smul_sum]
end PI.WFJM
