-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.ap_key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:17:59.531879+00:00
-- url     : https://prove2.me/submissions/923f8e5f-847d-4eed-935c-ffa4266b6919

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
theorem _root_.solution (η D : ℝ) (h8 : 8 ≤ η) (hD : 2 * η ≤ D) : 4 / η ^ 2 ≤ 1 / η - 1 / D := by
  have hη : 0 < η := by linarith
  have h1 : 1 / D ≤ 1 / (2 * η) := one_div_le_one_div_of_le (by positivity) hD
  have h2 : 4 / η ^ 2 ≤ 1 / η - 1 / (2 * η) := by
    rw [show 1 / η - 1 / (2 * η) = 1 / (2 * η) by field_simp; ring]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith
end ReciprocityTheory.L2DbarEstimates.I
