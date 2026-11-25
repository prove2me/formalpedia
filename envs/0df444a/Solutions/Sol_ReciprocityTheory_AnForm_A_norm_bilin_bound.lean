-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.norm_bilin_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:05:16.467531+00:00
-- url     : https://prove2.me/submissions/1109137c-b403-4ce6-9d87-706f84166174

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology
open scoped ContDiff Interval
noncomputable section
variable {ι : Type*} [Fintype ι] [Nonempty ι]
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] F →L[ℝ] G) (x : E) (y : F)
    (hy : x ≠ 0 → ‖y‖ ≤ 1 / 2) : ‖L x y‖ ≤ ‖L‖ * ‖x‖ * (1 / 2) := by
  have key : ‖x‖ * ‖y‖ ≤ ‖x‖ * (1 / 2) := by
    by_cases hx : x = 0
    · rw [hx, norm_zero, zero_mul, zero_mul]
    · exact mul_le_mul_of_nonneg_left (hy hx) (norm_nonneg _)
  calc ‖L x y‖ ≤ ‖L‖ * ‖x‖ * ‖y‖ := L.le_opNorm₂ _ _
    _ ≤ ‖L‖ * ‖x‖ * (1 / 2) := by
      rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_left key (norm_nonneg _)
end ReciprocityTheory.AnForm.A
