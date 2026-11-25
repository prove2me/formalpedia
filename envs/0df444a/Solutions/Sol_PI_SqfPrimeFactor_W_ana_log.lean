-- Prove2me | solution 1 for PI.SqfPrimeFactor.W.ana_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:24:07.611077+00:00
-- url     : https://prove2.me/submissions/a16622ec-87da-4502-8388-0d4df85d1f15

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PrimesDyadicRS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_AnaCore

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.SqfPrimeFactor PI.SqfPrimeFactor.W
open Finset
namespace PI.SqfPrimeFactor.W
theorem _root_.solution : Real.log 100 < 4.64 := by
  have h2 := Real.log_two_lt_d9
  have h128 : Real.log 128 = 7 * Real.log 2 := by
    rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]; norm_num
  have hq : Real.log 100 = Real.log 128 - Real.log (128 / 100) := by
    rw [Real.log_div (by norm_num) (by norm_num)]; ring
  have hl : 1 - (128 / 100 : ℝ)⁻¹ ≤ Real.log (128 / 100) :=
    Real.one_sub_inv_le_log_of_pos (by norm_num)
  norm_num at hl h2
  linarith
end PI.SqfPrimeFactor.W
