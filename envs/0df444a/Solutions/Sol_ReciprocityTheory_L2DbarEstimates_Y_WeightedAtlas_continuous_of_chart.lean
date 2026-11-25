-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.continuous_of_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:10:12.145878+00:00
-- url     : https://prove2.me/submissions/2a1fa7aa-06c6-45c2-a258-9eab9f0cdf1e

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxB
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr


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
theorem _root_.solution {E : Type*} [TopologicalSpace E] (f : Y → E)
    (hf : ∀ i, ContinuousOn (f ∘ (A.chart i).symm) (A.chart i).target) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun y => ?_
  have hy := A.mem_pick y
  set φ := A.chart (A.pick y)
  have h1 : ContinuousAt (f ∘ φ.symm) (φ y) :=
    (hf _).continuousAt (φ.open_target.mem_nhds (φ.map_source hy))
  have h2 : ContinuousAt (fun x => (f ∘ φ.symm) (φ x)) y := h1.comp (φ.continuousAt hy)
  refine h2.congr ?_
  filter_upwards [φ.open_source.mem_nhds hy] with x hx
  simp [φ.left_inv hx]
end ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
