-- Prove2me | solution 1 for PI.WFJM.minusPart1_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:18:54.553622+00:00
-- url     : https://prove2.me/submissions/c2f8bd10-9a0b-4401-8f15-aa4cf1d320c3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Theorems.Thm_PI_WFJM_minusPart_smul
import Theorems.Thm_PI_WFJM_minusPart_sum
import Theorems.Thm_PI_WFJM_fockAct1_expand

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
theorem _root_.solution (X : Mat p q) (P : Pol p q r s) :
    minusPart (fockAct1 p q r s X) P = ∑ a, ∑ b, X a b • minusPart (fockAct1 p q r s (Eab a b)) P := by
  rw [fockAct1_expand (r := r) (s := s) X, minusPart_sum]
  simp only [minusPart_sum, minusPart_smul]
end PI.WFJM
