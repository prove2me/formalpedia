-- Prove2me | solution 1 for PI.TailWork.log_five_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:29:40.546026+00:00
-- url     : https://prove2.me/submissions/d3f07589-95da-4e09-8355-54abcbe270a3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PrimeLogarithmTail_SumLogBlock
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PrimeLogarithmTail_SumLogDivSqLeDiv
import Theorems.Thm_PI_TailWork_log_three_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.TailWork
open Finset
namespace PI.TailWork
theorem _root_.solution : Real.log 5 ≤ 1.62 := by
  have h25 : Real.log 25 = 2 * Real.log 5 := by
    rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h24 : Real.log 24 = 3 * Real.log 2 + Real.log 3 := by
    rw [show (24 : ℝ) = 2 ^ 3 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    norm_num
  have hq : Real.log 25 - Real.log 24 ≤ 25 / 24 - 1 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    exact Real.log_le_sub_one_of_pos (by norm_num)
  linarith [Real.log_two_lt_d9, log_three_le]
end PI.TailWork
