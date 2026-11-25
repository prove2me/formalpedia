-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.hyq_smoothFn_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:24:58.621192+00:00
-- url     : https://prove2.me/submissions/6345a401-0165-45f2-8b68-b27c2178d1f2

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLoc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNull
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ContDiffAtSectionFrameQuotient
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fn_hom_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.L2DbarEstimates.Y.fn_hom_zero



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas Metric
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (A : WeightedAtlas n Y ι La) {f : Y → ℝ} (hf : A.SmoothFn f) :
    Continuous f := by
  rw [continuous_iff_continuousAt]
  intro y
  have hy := A.mem_pick y
  have h1 : ContinuousOn (f ∘ (A.chart (A.pick y)).symm) (A.chart (A.pick y)).target :=
    (hf (A.pick y)).continuousOn
  have h2 : ContinuousAt (f ∘ (A.chart (A.pick y)).symm) (A.chart (A.pick y) y) :=
    h1.continuousAt ((A.chart (A.pick y)).open_target.mem_nhds ((A.chart (A.pick y)).map_source hy))
  refine (h2.comp ((A.chart (A.pick y)).continuousAt hy)).congr ?_
  filter_upwards [(A.chart (A.pick y)).open_source.mem_nhds hy] with x hx
  simp [(A.chart (A.pick y)).left_inv hx]
end ReciprocityTheory.L2DbarEstimates.Y
