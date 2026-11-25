-- Prove2me | solution 1 for PI.EF.Rect.log_neg_sub_log_of_im_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:36:47.8919+00:00
-- url     : https://prove2.me/submissions/662cde6a-3473-4704-a240-f3331e1741c4

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
theorem _root_.solution {b : ℂ} (hb : b.im < 0) : Complex.log (-b) - Complex.log b = π * I := by
  have h := Complex.arg_neg_eq_arg_add_pi_of_im_neg hb
  apply Complex.ext
  · simp [Complex.log_re]
  · simp [Complex.log_im, h]
end PI.EF.Rect
