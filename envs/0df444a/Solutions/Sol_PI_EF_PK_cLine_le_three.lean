-- Prove2me | solution 1 for PI.EF.PK.cLine_le_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:36:57.326714+00:00
-- url     : https://prove2.me/submissions/e477cc65-38b2-4a37-bea7-e66437269854

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronTruncOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_ContinuousInvSqrt

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
theorem _root_.solution {u : ℝ} (hu : 2 ≤ u) : cLine u ≤ 3 := by
  unfold cLine
  have h2 : (1 : ℝ) / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hl : Real.log 2 ≤ Real.log u := Real.log_le_log (by norm_num) hu
  have hpos : 0 < Real.log u := by linarith
  have h3 : 1 / Real.log u ≤ 2 := by rw [div_le_iff₀ hpos]; linarith
  linarith
end PI.EF.PK
