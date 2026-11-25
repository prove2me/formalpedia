-- Prove2me | solution 1 for PI.EF.Rect.log_sub_log_neg_of_im_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:36:50.761954+00:00
-- url     : https://prove2.me/submissions/e13dc18c-5f5d-423e-b9fc-289e18127e4c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_RectIntEqZeroOfDifferentiableOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF PI.EF.Rect
open Complex MeasureTheory intervalIntegral Set Filter Topology Real
namespace PI.EF.Rect
theorem _root_.solution {a : ℂ} (ha : 0 < a.im) : Complex.log a - Complex.log (-a) = π * I := by
  have h := Complex.arg_neg_eq_arg_sub_pi_of_im_pos ha
  apply Complex.ext
  · simp [Complex.log_re]
  · simp [Complex.log_im, h]
end PI.EF.Rect
