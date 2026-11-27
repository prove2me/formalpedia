-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.B.isWeakD_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:29:08.92672+00:00
-- url     : https://prove2.me/submissions/1ef29929-e428-42cb-bf67-0365e8a59c93

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_MollifierL2LocTendsto

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
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (m : ℕ) (c : Fin m → ℂ) (v : Fin m → E) :
    IsWeakD μ c v (fun _ => 0) 0 := by
  refine ⟨fun _ => locallyIntegrable_zero, locallyIntegrable_zero, fun φ _ _ => ?_⟩
  simp
end ReciprocityTheory.L2DbarEstimates.B
