-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.deriv_extCh_of_two_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:09.990802+00:00
-- url     : https://prove2.me/submissions/7dfd5893-8f4e-4def-921f-15fe549aa1de

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtWeakA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_extCh_of_two_le

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
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution {t : ℝ} (ht : 2 < t) : deriv extCh t = 0 := by
  have h : extCh =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact extCh_of_two_le (le_of_lt hs)
  rw [h.deriv_eq]
  simp
end ReciprocityTheory.L2DbarEstimates.C
