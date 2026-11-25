-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.sh_num
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:19:29.343258+00:00
-- url     : https://prove2.me/submissions/722211fc-24dc-4e20-b9b3-1d04bbdaa690

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ShellA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology Set
open scoped ENNReal ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution (τ : ℝ) (hτ : 0 < τ) :
    Real.exp (min (τ / 10) (1 / 4)) * (Real.log 2 + 2 * min (τ / 10) (1 / 4)) ≤
      (1 + τ) * Real.log 2 := by
  set θ := min (τ / 10) (1 / 4) with hθ
  have h0 : 0 < θ := lt_min (by positivity) (by norm_num)
  have h1 : θ ≤ τ / 10 := min_le_left _ _
  have h2 : θ ≤ 1 / 4 := min_le_right _ _
  have hexp : Real.exp θ ≤ 1 + 2 * θ := by
    have := Real.exp_bound_div_one_sub_of_interval' h0 (by linarith)
    have h3 : 1 / (1 - θ) ≤ 1 + 2 * θ := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  have hl1 := Real.log_two_gt_d9
  have hl2 := Real.log_two_lt_d9
  have hpos : 0 ≤ Real.log 2 + 2 * θ := by linarith
  calc Real.exp θ * (Real.log 2 + 2 * θ) ≤ (1 + 2 * θ) * (Real.log 2 + 2 * θ) :=
        mul_le_mul_of_nonneg_right hexp hpos
    _ ≤ (1 + τ) * Real.log 2 := by nlinarith
end ReciprocityTheory.L2DbarEstimates.I
