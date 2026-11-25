-- Prove2me | solution 1 for PI.EF.PK.left_side
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:42:36.718007+00:00
-- url     : https://prove2.me/submissions/7d66c0f1-e158-434e-923a-259d33c2ae1d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronTruncOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_ContinuousInvSqrt
import Theorems.Thm_PI_EF_PK_continuous_inv_sqrt
import Theorems.Thm_PI_EF_PK_integral_inv_sqrt
import Theorems.Thm_PI_EF_PK_norm_upow_div_left

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
theorem _root_.solution (G : ℂ → ℂ) (u T' K2 : ℝ) (hu : 1 ≤ u) (hT'0 : 0 < T') (hK20 : 0 ≤ K2)
    (hb : ∀ t : ℝ, |t| ≤ T' → ‖G (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ≤ K2) :
    ‖∫ t : ℝ in -T'..T', G (((-1 / 2 : ℝ) : ℂ) + t * I) *
        ((u : ℂ) ^ (((-1 / 2 : ℝ) : ℂ) + t * I) / (((-1 / 2 : ℝ) : ℂ) + t * I))‖ ≤
      K2 * (2 * Real.arsinh (2 * T')) := by
  have hle : -T' ≤ T' := by linarith
  calc _ ≤ ∫ t in -T'..T', K2 * (2 * (√(1 + (2 * t) ^ 2))⁻¹) := by
        refine intervalIntegral.norm_integral_le_of_norm_le hle
          (Filter.Eventually.of_forall (fun t ht => ?_))
          ((continuous_const.mul continuous_inv_sqrt).intervalIntegrable _ _)
        rw [norm_mul]
        have ht' : |t| ≤ T' := abs_le.mpr ⟨ht.1.le, ht.2⟩
        exact mul_le_mul (hb t ht') (norm_upow_div_left u hu t) (norm_nonneg _) hK20
    _ = K2 * (2 * Real.arsinh (2 * T')) := by
        rw [intervalIntegral.integral_const_mul, integral_inv_sqrt]
end PI.EF.PK
