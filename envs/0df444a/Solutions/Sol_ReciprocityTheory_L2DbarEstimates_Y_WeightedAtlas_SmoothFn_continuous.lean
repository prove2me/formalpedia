-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.SmoothFn.continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:25:11.581966+00:00
-- url     : https://prove2.me/submissions/4f05ee54-2928-407a-b62c-52ffab0d4ce6

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxB
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_continuous_of_chart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology
open scoped ContDiff ENNReal
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)
namespace ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
namespace SmoothFn
theorem _root_.solution {f : Y → ℝ} (hf : A.SmoothFn f) : Continuous f :=
  A.continuous_of_chart f fun i => (hf i).continuousOn
end SmoothFn
end ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
