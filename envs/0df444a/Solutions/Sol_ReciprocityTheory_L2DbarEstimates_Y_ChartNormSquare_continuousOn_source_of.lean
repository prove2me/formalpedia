-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.ChartNormSquare.continuousOn_source_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:19:26.888302+00:00
-- url     : https://prove2.me/submissions/e18fa63f-7ade-4e7b-9dce-525e6f0425fc

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AExact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.ChartNormSquare
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
namespace ReciprocityTheory.L2DbarEstimates.Y.ChartNormSquare
theorem _root_.solution {E : Type*} [TopologicalSpace E] (e : OpenPartialHomeomorph Y (V n))
    (f : Y → E) (h : ContinuousOn (f ∘ e.symm) e.target) : ContinuousOn f e.source := by
  refine (h.comp e.continuousOn e.mapsTo).congr ?_
  intro y hy
  simp [Function.comp, e.left_inv hy]
end ReciprocityTheory.L2DbarEstimates.Y.ChartNormSquare
