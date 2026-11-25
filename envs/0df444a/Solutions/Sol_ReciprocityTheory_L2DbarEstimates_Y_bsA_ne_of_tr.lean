-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.bsA_ne_of_tr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:22:25.010804+00:00
-- url     : https://prove2.me/submissions/1e493c90-a54c-4d03-ad5a-b61159dbf551

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLoc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepA

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
open scoped ContDiff ENNReal
noncomputable section
universe u
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {la : La} {U : Set Y} {a : ι → Y → ℂ} (ha : bsTr A la U a) {i j : ι}
    {y : Y} (hy : y ∈ U) (hi : y ∈ (A.chart i).source) (hj : y ∈ (A.chart j).source)
    (h : a j y ≠ 0) : a i y ≠ 0 := by
  unfold bsTr at ha
  rw [ha i j y hy hi hj]
  exact mul_ne_zero (A.g_ne la i j y hi hj) h
end ReciprocityTheory.L2DbarEstimates.Y
