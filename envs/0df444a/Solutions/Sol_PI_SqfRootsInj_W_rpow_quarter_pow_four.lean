-- Prove2me | solution 1 for PI.SqfRootsInj.W.rpow_quarter_pow_four
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:31:26.063811+00:00
-- url     : https://prove2.me/submissions/41555625-76a3-450f-9ee9-747f250914e5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_SumSqPowLeTwo
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_RpowQuarterPowFour

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Classical
open PI PI.SqfRootsInj PI.SqfRootsInj.W
open PI.SqfLab
namespace PI.SqfRootsInj.W
theorem _root_.solution (x : ℝ) (hx : 0 ≤ x) : (x ^ ((1 : ℝ) / 4)) ^ 4 = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num
end PI.SqfRootsInj.W
