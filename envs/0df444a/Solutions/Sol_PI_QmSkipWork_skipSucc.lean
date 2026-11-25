-- Prove2me | solution 1 for PI.QmSkipWork.skipSucc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:06:54.440451+00:00
-- url     : https://prove2.me/submissions/ba7b93f5-0d6c-4240-9987-0824ca36436b

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
theorem _root_.solution : PI.SkipSucc := by
  unfold PI.SkipSucc
  intro t i j
  apply Fin.ext
  rw [PI.QmSkipWork.val_succAbove]
  unfold PI.skip1
  split_ifs <;> rfl
end PI.QmSkipWork
