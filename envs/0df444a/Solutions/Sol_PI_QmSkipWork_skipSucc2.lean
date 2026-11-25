-- Prove2me | solution 1 for PI.QmSkipWork.skipSucc2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:06:59.185467+00:00
-- url     : https://prove2.me/submissions/632db703-4d03-49a5-9442-7438cff12822

import Definitions.Def_Formalism_PeriodIntegrals_QmSkip
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SkipSuccessorIndex_SkipSucc2
import Theorems.Thm_PI_QmSkipWork_val_succAbove

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.QmSkipWork
namespace PI.QmSkipWork
theorem _root_.solution : PI.SkipSucc2 := by
  unfold PI.SkipSucc2
  intro t i i' j hii'
  have hb : (i.succAbove i').val = i'.val + 1 := by
    rw [PI.QmSkipWork.val_succAbove, if_neg (by omega)]
  apply Fin.ext
  simp only [PI.QmSkipWork.val_succAbove]
  unfold PI.skip2
  split_ifs <;> (try dsimp only) <;> omega
end PI.QmSkipWork
