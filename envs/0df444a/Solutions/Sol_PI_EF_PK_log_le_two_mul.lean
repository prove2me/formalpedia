-- Prove2me | solution 1 for PI.EF.PK.log_le_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:36:44.953617+00:00
-- url     : https://prove2.me/submissions/fda82a97-9f6a-4bf2-96e4-b4fa8a0d2b02

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
theorem _root_.solution {X Y : ℝ} (hX : 0 < X) (hXY : X ≤ Y ^ 2) : Real.log X ≤ 2 * Real.log Y := by
  calc Real.log X ≤ Real.log (Y ^ 2) := Real.log_le_log hX hXY
    _ = 2 * Real.log Y := by rw [Real.log_pow]; push_cast; ring
end PI.EF.PK
