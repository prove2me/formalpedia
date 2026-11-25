-- Prove2me | solution 1 for P2M_PI_WFJM_minusPart_omE_np__e671a62cbaae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:43:40.372277+00:00
-- url     : https://prove2.me/submissions/d51d343f-9abe-4a90-bfa8-ca0c28740edf

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Theorems.Thm_PI_WFJM_dd_comm
import Theorems.Thm_PI_WFJM_minusPart_omE_np

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
namespace PI.WFJM
theorem _root_.solution {p q r s : ℕ} (l l' : Ln p q r s) (h : linePos l = false) (h' : linePos l' = true)
    (P : Pol p q r s) : minusPart (omE l l') P = -(dd l' l P) := by
  rw [minusPart_omE_np l l' h h' P, dd_comm]
end PI.WFJM
