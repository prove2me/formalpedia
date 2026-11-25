-- Prove2me | solution 1 for PI.SSE.small_of_im
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:17:21.49626+00:00
-- url     : https://prove2.me/submissions/40efe87b-bb82-4e7b-b79e-6c9f782eda79

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_ThetaDerivNe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_ThetaNz

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex
open PI PI.SSE
namespace PI.SSE
theorem _root_.solution (y : ℝ) (hy : 0 < y) (h3 : 3 ≤ 4 * y ^ 2) :
    3 * Real.exp (-(2 * Real.pi * y)) < 1 / 2 := by
  have hy2 : 1 / 2 < y := by nlinarith
  have hx : 3 < 2 * Real.pi * y := by nlinarith [Real.pi_gt_three]
  have he : 6 < Real.exp (2 * Real.pi * y) := by
    have h := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 2 * Real.pi * y by positivity)
    nlinarith
  have hp := Real.exp_pos (2 * Real.pi * y)
  rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_iff₀ hp]
  linarith
end PI.SSE
