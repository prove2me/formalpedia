-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.logCutoff_eq_one
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:05:25.941643+00:00
-- url     : https://prove2.me/submissions/df1e938c-517f-410f-8f42-cc6bd94133a9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtWeakA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_extCh_of_le_one

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
open scoped ENNReal ContDiff
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution {F : V n → ℂ} {k : ℝ} (hk : 0 < k) {z : V n} (hz : F z ≠ 0)
    (h : -Real.log (‖F z‖ ^ 2) ≤ k) : extCut F k z = 1 := by
  simp only [extCut, hz, if_false]
  exact extCh_of_le_one ((div_le_one hk).2 h)
end ReciprocityTheory.L2DbarEstimates.C
