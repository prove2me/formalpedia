-- Prove2me | solution 1 for PI.WFJM.omE_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:12:28.872535+00:00
-- url     : https://prove2.me/submissions/18e3b5b0-c581-48e0-bbb3-e531e2d4028e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr

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
namespace PI.WFJM
theorem _root_.solution {p q r s : ℕ} {l l' : Ln p q r s} (h : l ≠ l') : omE l l' = raiB l * lowB l' := by
  rw [FockH1Action.omE, if_neg h, add_zero]
end PI.WFJM
