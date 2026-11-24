-- Prove2me | solution 1 for PI.WFJM.rightOffDiagonalActionFormula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:40.132549+00:00
-- url     : https://prove2.me/submissions/3e5b07f9-2cd0-4f14-9e1a-d862564b8f0f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Theorems.Thm_PI_WFJM_omE_ne
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
namespace PI.WFJM
theorem _root_.solution : FormRaise2 := by
  intro p q r s c d hcd
  rw [fockAct2_Eab, PI.FJM.rai2]
  refine Finset.sum_congr rfl fun a _ => omE_ne ?_
  intro h
  exact hcd (congrArg Prod.snd h)
end PI.WFJM
