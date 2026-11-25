-- Prove2me | solution 1 for PI.PrimeLogOverPWork.S_le_31_63
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:17:24.288815+00:00
-- url     : https://prove2.me/submissions/bfefb0db-d4d9-4476-bf69-eb11621aa72c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_LogFactorialEqSumLog
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_SLeOfBlock
import Theorems.Thm_PI_PrimeLogOverPWork_u3
import Theorems.Thm_PI_PrimeLogOverPWork_u5
import Theorems.Thm_PI_PrimeLogOverPWork_u7
import Theorems.Thm_PI_PrimeLogOverPWork_u11
import Theorems.Thm_PI_PrimeLogOverPWork_u13
import Theorems.Thm_PI_PrimeLogOverPWork_u17
import Theorems.Thm_PI_PrimeLogOverPWork_u19
import Theorems.Thm_PI_PrimeLogOverPWork_u23
import Theorems.Thm_PI_PrimeLogOverPWork_u29
import Theorems.Thm_PI_PrimeLogOverPWork_u37
import Theorems.Thm_PI_PrimeLogOverPWork_u41
import Theorems.Thm_PI_PrimeLogOverPWork_u43
import Theorems.Thm_PI_PrimeLogOverPWork_u47
import Theorems.Thm_PI_PrimeLogOverPWork_u53
import Theorems.Thm_PI_PrimeLogOverPWork_u59
import Theorems.Thm_PI_PrimeLogOverPWork_u61
import Theorems.Thm_PI_PrimeLogOverPWork_l31
import Theorems.Thm_PI_PrimeLogOverPWork_S_63

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
theorem _root_.solution : S 63 ≤ Real.log (31 : ℝ) := by
  rw [S_63]
  have h2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have ha := l31
  have hb0 := u3
  have hb1 := u5
  have hb2 := u7
  have hb3 := u11
  have hb4 := u13
  have hb5 := u17
  have hb6 := u19
  have hb7 := u23
  have hb8 := u29
  have hb9 := u37
  have hb10 := u41
  have hb11 := u43
  have hb12 := u47
  have hb13 := u53
  have hb14 := u59
  have hb15 := u61
  linarith
end PI.PrimeLogOverPWork
