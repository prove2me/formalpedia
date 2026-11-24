-- Prove2me | solution 1 for PI.WFJM.ne_of_linePos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:57:13.022859+00:00
-- url     : https://prove2.me/submissions/2d8e8e2b-efee-40de-8520-70bd625b5a74

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
open PI.FJM
namespace PI.WFJM
theorem _root_.solution {p q r s : ℕ} {l l' : Ln p q r s} (h : linePos l ≠ linePos l') : l ≠ l' := by
  rintro rfl
  exact h rfl
end PI.WFJM
