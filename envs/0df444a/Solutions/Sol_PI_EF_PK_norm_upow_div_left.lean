-- Prove2me | solution 1 for PI.EF.PK.norm_upow_div_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:36:50.696379+00:00
-- url     : https://prove2.me/submissions/c150b259-9d31-4342-bc28-04cb21f8447c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronTruncOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_ContinuousInvSqrt
import Theorems.Thm_PI_EF_PK_norm_upow_div

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
theorem _root_.solution (u : ℝ) (hu : 1 ≤ u) (t : ℝ) :
    ‖(u : ℂ) ^ (((-1 / 2 : ℝ) : ℂ) + t * I) / (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ≤
      2 * (√(1 + (2 * t) ^ 2))⁻¹ := by
  have hsq : 0 < √(1 + (2 * t) ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hm : 0 < √(1 + (2 * t) ^ 2) / 2 := by positivity
  have hsm : √(1 + (2 * t) ^ 2) / 2 ≤ ‖(((-1 / 2 : ℝ) : ℂ) + t * I)‖ := by
    rw [Complex.norm_add_mul_I, Real.le_sqrt hm.le, div_pow, Real.sq_sqrt (by positivity)]
    · exact le_of_eq (by ring)
    · positivity
  have h1 := norm_upow_div u hu (((-1 / 2 : ℝ) : ℂ) + t * I) (-1 / 2) _ hm (by simp) hsm
  calc _ ≤ u ^ (-1 / 2 : ℝ) / (√(1 + (2 * t) ^ 2) / 2) := h1
    _ ≤ 1 / (√(1 + (2 * t) ^ 2) / 2) := by
        gcongr
        exact Real.rpow_le_one_of_one_le_of_nonpos hu (by norm_num)
    _ = 2 * (√(1 + (2 * t) ^ 2))⁻¹ := by field_simp
end PI.EF.PK
