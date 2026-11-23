-- Prove2me | solution 1 for PI.EF.PK.norm_upow_div
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:12.984799+00:00
-- url     : https://prove2.me/submissions/3c7d81b7-906d-417f-956c-912ba6db9852

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
theorem _root_.solution (u : ℝ) (hu : 1 ≤ u) (s : ℂ) (c m : ℝ) (hm : 0 < m) (hsc : s.re ≤ c)
    (hsm : m ≤ ‖s‖) : ‖(u : ℂ) ^ s / s‖ ≤ u ^ c / m := by
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
  exact div_le_div₀ (Real.rpow_pos_of_pos (by linarith) _).le
    (Real.rpow_le_rpow_of_exponent_le hu hsc) hm hsm
end PI.EF.PK
