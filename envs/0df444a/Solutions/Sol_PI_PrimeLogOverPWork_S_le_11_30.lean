-- Prove2me | solution 1 for PI.PrimeLogOverPWork.S_le_11_30
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:11:50.944515+00:00
-- url     : https://prove2.me/submissions/f99d9f29-253c-4b84-b695-dc38863b3ef8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_LogFactorialEqSumLog
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_SLeOfBlock
import Theorems.Thm_PI_PrimeLogOverPWork_u3
import Theorems.Thm_PI_PrimeLogOverPWork_u5
import Theorems.Thm_PI_PrimeLogOverPWork_u7
import Theorems.Thm_PI_PrimeLogOverPWork_u13
import Theorems.Thm_PI_PrimeLogOverPWork_u17
import Theorems.Thm_PI_PrimeLogOverPWork_u19
import Theorems.Thm_PI_PrimeLogOverPWork_u23
import Theorems.Thm_PI_PrimeLogOverPWork_u29
import Theorems.Thm_PI_PrimeLogOverPWork_l11
import Theorems.Thm_PI_PrimeLogOverPWork_S_30

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.PrimeLogOverPWork
open Finset
namespace PI.PrimeLogOverPWork
theorem _root_.solution : S 30 ≤ Real.log (11 : ℝ) := by
  rw [S_30]
  have h2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have ha := l11
  have hb0 := u3
  have hb1 := u5
  have hb2 := u7
  have hb3 := u13
  have hb4 := u17
  have hb5 := u19
  have hb6 := u23
  have hb7 := u29
  linarith
end PI.PrimeLogOverPWork
