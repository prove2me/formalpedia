-- Prove2me | solution 1 for PI.EF.PK.continuous_inv_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:12.224021+00:00
-- url     : https://prove2.me/submissions/ab4f2946-d596-4638-8602-aa8adab33f94

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
theorem _root_.solution : Continuous fun t : ℝ => 2 * (√(1 + (2 * t) ^ 2))⁻¹ :=
  continuous_const.mul ((continuous_const.add ((continuous_const.mul continuous_id).pow 2)).sqrt.inv₀
    (fun t => (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < 1 + (2 * t) ^ 2)).ne'))
end PI.EF.PK
