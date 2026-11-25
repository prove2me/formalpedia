-- Prove2me | solution 1 for PI.EF.PK.arsinh_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:36:55.550997+00:00
-- url     : https://prove2.me/submissions/47cd2fea-d5fe-4d77-b359-40296772a56f

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
theorem _root_.solution (x : ℝ) (hx : 0 ≤ x) : Real.arsinh x ≤ Real.log (1 + 2 * x) := by
  have hs0 : 0 < √(1 + x ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hs : √(1 + x ^ 2) ≤ 1 + x := by
    rw [Real.sqrt_le_iff]
    constructor
    · linarith
    · nlinarith
  unfold Real.arsinh
  exact Real.log_le_log (by linarith) (by linarith)
end PI.EF.PK
