-- Prove2me | solution 1 for PI.SqfRootsInj.W.rpow_neg_half_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:26:30.259924+00:00
-- url     : https://prove2.me/submissions/12bb5a5b-6773-43ef-a3fe-72e0bbabe228

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
theorem _root_.solution (x : ℝ) (hx : 0 ≤ x) :
    x ^ (-(1 / 2 : ℝ)) = ((x ^ ((1 : ℝ) / 4))⁻¹) ^ 2 := by
  rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_mul hx, Real.rpow_neg hx]; norm_num
end PI.SqfRootsInj.W
