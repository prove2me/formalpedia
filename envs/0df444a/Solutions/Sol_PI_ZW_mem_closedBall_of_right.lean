-- Prove2me | solution 1 for PI.ZW.mem_closedBall_of_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:16:02.006814+00:00
-- url     : https://prove2.me/submissions/ed3ae3fe-b63a-434d-8a6b-1ae9e788d42b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightHalfWith
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightChi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Metric Complex
open PI PI.ZW
namespace PI.ZW
theorem _root_.solution {ρ : ℂ} {t : ℝ} (h1 : 1 / 2 ≤ ρ.re) (h2 : ρ.re < 1) (h3 : |ρ.im - t| ≤ 1) :
    ρ ∈ closedBall (2 + t * I) (37 / 20) := by
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hsq : ‖ρ - (2 + t * I)‖ ^ 2 ≤ (37 / 20) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    have h4 := abs_le.mp h3
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) (by linarith : (0 : ℝ) ≤ 7 / 2 - ρ.re),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - (ρ.im - t)) (by linarith : (0 : ℝ) ≤ 1 + (ρ.im - t))]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by norm_num) two_ne_zero).mp hsq
end PI.ZW
