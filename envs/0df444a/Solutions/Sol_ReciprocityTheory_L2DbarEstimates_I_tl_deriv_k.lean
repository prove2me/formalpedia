-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.tl_deriv_k
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:06:07.633784+00:00
-- url     : https://prove2.me/submissions/6d75feb3-f76e-46e1-95fd-59248e6af837

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_CommFderivApply
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ExistsChartPartition
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_TwistLeviA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_tlK_eventually
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_tl_hasDerivAt_k
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_tl_hasDerivAt_kp

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
noncomputable section
open Filter Topology
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution (c t : ℝ) (ht : t ≤ c - 1) :
    deriv (tlK c) t = tlKp c t ∧ deriv (deriv (tlK c)) t = tlKpp c t := by
  have ht' : t < c - 19 / 20 := by linarith
  have hE : deriv (tlK c) =ᶠ[𝓝 t] tlKp c := by
    filter_upwards [Iio_mem_nhds ht'] with y hy
    simp only [Set.mem_Iio] at hy
    exact ((tl_hasDerivAt_k c y (by linarith)).congr_of_eventuallyEq (tlK_eventually c y hy)).deriv
  refine ⟨hE.eq_of_nhds, ?_⟩
  exact ((tl_hasDerivAt_kp c t (by linarith)).congr_of_eventuallyEq hE).deriv
end ReciprocityTheory.L2DbarEstimates.I
