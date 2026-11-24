-- Prove2me | solution 1 for PI.WFJM.leftOffDiagonalActionFormula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:03.169256+00:00
-- url     : https://prove2.me/submissions/326dc54e-efaa-42cf-898c-316c00be51af

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Theorems.Thm_PI_WFJM_omE_ne
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
namespace PI.WFJM
theorem _root_.solution : FormRaise1 := by
  intro p q r s a b hab
  rw [fockAct1_Eab, PI.FJM.rai1]
  refine Finset.sum_congr rfl fun c _ => omE_ne ?_
  intro h
  exact hab (congrArg Prod.fst h)
end PI.WFJM
