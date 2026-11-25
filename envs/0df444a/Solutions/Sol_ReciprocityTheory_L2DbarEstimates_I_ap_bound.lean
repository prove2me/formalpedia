-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.ap_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:18:21.784814+00:00
-- url     : https://prove2.me/submissions/d3ffe12b-924b-4c1e-b4a2-85aaa62c60ff

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ApplyB
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ApplyC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution (D ε η Θ : ℝ) (G B : ℂ) (hε : 0 < ε) (hD : |D| ≤ 3)
    (hB : ‖B‖ ^ 2 ≤ 4 * ε ^ 4 * η * Θ) (hη : 0 ≤ η) (hΘ : 0 ≤ Θ) :
    ‖((D * (1 / ε ^ 2) : ℝ) : ℂ) * G * B‖ ^ 2 ≤ 36 * η * ‖G‖ ^ 2 * Θ := by
  have e1 : ‖((D * (1 / ε ^ 2) : ℝ) : ℂ) * G * B‖ ^ 2 = D ^ 2 * ‖G‖ ^ 2 * ‖B‖ ^ 2 / ε ^ 4 := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, mul_pow, abs_mul,
      mul_pow, sq_abs, abs_of_pos (by positivity : (0:ℝ) < 1 / ε ^ 2)]
    field_simp
  have hD2 : D ^ 2 ≤ 9 := by
    have := sq_le_sq' (abs_le.1 hD).1 (abs_le.1 hD).2
    linarith
  rw [e1]
  have hε4 : 0 < ε ^ 4 := by positivity
  rw [div_le_iff₀ hε4]
  have hG : 0 ≤ ‖G‖ ^ 2 := by positivity
  calc D ^ 2 * ‖G‖ ^ 2 * ‖B‖ ^ 2 ≤ D ^ 2 * ‖G‖ ^ 2 * (4 * ε ^ 4 * η * Θ) :=
        mul_le_mul_of_nonneg_left hB (by positivity)
    _ = D ^ 2 * (4 * ε ^ 4 * (η * ‖G‖ ^ 2 * Θ)) := by ring
    _ ≤ 9 * (4 * ε ^ 4 * (η * ‖G‖ ^ 2 * Θ)) :=
        mul_le_mul_of_nonneg_right hD2 (by positivity)
    _ = 36 * η * ‖G‖ ^ 2 * Θ * ε ^ 4 := by ring
end ReciprocityTheory.L2DbarEstimates.I
