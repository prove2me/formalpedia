-- Prove2me | solution 1 for PI.EF.PK.rpow_cLine_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:36:52.60703+00:00
-- url     : https://prove2.me/submissions/ba79f6a6-5233-4ee0-a499-f03b70e030ca

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
theorem _root_.solution {u : ℝ} (hu : 2 ≤ u) : u ^ cLine u ≤ 3 * u := by
  have hu0 : 0 < u := by linarith
  have hl : 0 < Real.log u := Real.log_pos (by linarith)
  unfold cLine
  rw [Real.rpow_add hu0, Real.rpow_one, Real.rpow_def_of_pos hu0, mul_one_div_cancel hl.ne']
  have := Real.exp_one_lt_d9
  nlinarith
end PI.EF.PK
