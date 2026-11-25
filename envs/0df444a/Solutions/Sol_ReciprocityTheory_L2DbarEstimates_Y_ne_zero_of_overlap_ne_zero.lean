-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.ne_zero_of_overlap_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:13:39.518465+00:00
-- url     : https://prove2.me/submissions/3135a1c2-4a25-4725-87b9-7043825475ae

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DifferentiableAtLocalCoordinates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas Asymptotics
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (A : WeightedAtlas n Y ι La) (la : La) (w0 : ι → Y → ℂ)
    (hw : A.IsSec la w0) (i j : ι) (y : Y)
    (hi : y ∈ (A.chart i).source) (hj : y ∈ (A.chart j).source) (h : w0 j y ≠ 0) :
    w0 i y ≠ 0 := by
  rw [hw.2 i j y (Set.mem_univ y) hi hj]
  exact mul_ne_zero (A.g_ne la i j y hi hj) h
end ReciprocityTheory.L2DbarEstimates.Y
