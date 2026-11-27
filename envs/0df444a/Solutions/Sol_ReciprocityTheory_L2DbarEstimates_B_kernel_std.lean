-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.B.kernel_std
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:29:13.290803+00:00
-- url     : https://prove2.me/submissions/e83afa52-e99f-4763-8750-e2ba2fc41fae

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_MollifierL2LocTendsto
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_HasCompactSupport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.B
open MeasureTheory Filter Topology Set Metric
open scoped Convolution ContDiff ENNReal Pointwise
namespace ReciprocityTheory.L2DbarEstimates.B
theorem _root_.solution (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] : StdSt E μ := by
  have h : (fun ε : ℝ => (Kernel.std E μ ε).r) =ᶠ[𝓝[>] 0] id := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simp [Kernel.std, Kernel.ofBump, stdBump, show (0 : ℝ) < ε from hε]
  exact (tendsto_congr' h).2 (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)
end ReciprocityTheory.L2DbarEstimates.B
