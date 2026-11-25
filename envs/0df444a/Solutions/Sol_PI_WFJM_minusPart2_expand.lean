-- Prove2me | solution 1 for PI.WFJM.minusPart2_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:18:55.846389+00:00
-- url     : https://prove2.me/submissions/c0403bd1-bf13-4731-a57b-4c53b8c13b53

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Theorems.Thm_PI_WFJM_minusPart_smul
import Theorems.Thm_PI_WFJM_minusPart_sum
import Theorems.Thm_PI_WFJM_fockAct2_expand

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
theorem _root_.solution (Y : Mat r s) (P : Pol p q r s) :
    minusPart (fockAct2 p q r s Y) P = ∑ c, ∑ d, Y c d • minusPart (fockAct2 p q r s (Eab c d)) P := by
  rw [fockAct2_expand (p := p) (q := q) Y, minusPart_sum]
  simp only [minusPart_sum, minusPart_smul]
end PI.WFJM
