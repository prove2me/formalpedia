-- Prove2me | solution 1 for PI.EF.PK.ker_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:37:08.218931+00:00
-- url     : https://prove2.me/submissions/211ce744-e7b5-4d5d-871c-3458a135b270

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_RectInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronKernelA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.EF PI.EF.PK
open Complex MeasureTheory intervalIntegral Real
namespace PI.EF.PK
theorem _root_.solution (l : ℝ) {s : ℂ} (hs : s ≠ 0) : ker l s = gl l s + 1 / (s - 0) := by
  unfold gl ker
  rw [dslope_of_ne _ hs, slope_def_field]
  simp only [mul_zero, Complex.exp_zero, sub_zero]
  ring
end PI.EF.PK
