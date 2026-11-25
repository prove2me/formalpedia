-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.abs_second_variation_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:02:05.405997+00:00
-- url     : https://prove2.me/submissions/f93db063-6f52-4f54-a808-41840fa6ebdc

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCutA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCutB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution {p1 p2 x y z c1 c2 X Y Z : ℝ} (h1 : |p1| ≤ c1) (h2 : |p2| ≤ c2) (hx : |x| ≤ X)
    (hy : |y| ≤ Y) (hz : |z| ≤ Z) :
    |p2 * (2 * x) * (2 * x) + p1 * (2 * (y + z))| ≤ c2 * (2 * X) * (2 * X) + c1 * (2 * (Y + Z)) := by
  have hX : 0 ≤ X := (abs_nonneg x).trans hx
  have hc2 : 0 ≤ c2 := (abs_nonneg _).trans h2
  have hc1 : 0 ≤ c1 := (abs_nonneg _).trans h1
  have hx2 : 2 * |x| ≤ 2 * X := by linarith
  have hA : |p2 * (2 * x) * (2 * x)| ≤ c2 * (2 * X) * (2 * X) := by
    rw [abs_mul, abs_mul, abs_mul, abs_two]
    exact mul_le_mul (mul_le_mul h2 hx2 (by positivity) hc2) hx2 (by positivity)
      (mul_nonneg hc2 (by linarith))
  have hyz : |y + z| ≤ Y + Z := (abs_add_le _ _).trans (add_le_add hy hz)
  have hB : |p1 * (2 * (y + z))| ≤ c1 * (2 * (Y + Z)) := by
    rw [abs_mul, abs_mul, abs_two]
    exact mul_le_mul h1 (by linarith) (by positivity) hc1
  exact (abs_add_le _ _).trans (add_le_add hA hB)
end ReciprocityTheory.L2DbarEstimates.C
