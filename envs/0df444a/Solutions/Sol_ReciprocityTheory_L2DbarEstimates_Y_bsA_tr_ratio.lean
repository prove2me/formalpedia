-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.bsA_tr_ratio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:21:22.411053+00:00
-- url     : https://prove2.me/submissions/3afd8c5e-dec8-42fb-b69f-e33875d37298

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
theorem _root_.solution {la : La} {U : Set Y} {a b : ι → Y → ℂ} (ha : bsTr A la U a)
    (hb : bsTr A la U b) {i j : ι} {y : Y} (hy : y ∈ U) (hi : y ∈ (A.chart i).source)
    (hj : y ∈ (A.chart j).source) : a i y / b i y = a j y / b j y := by
  unfold bsTr at ha hb
  rw [ha i j y hy hi hj, hb i j y hy hi hj, mul_div_mul_left _ _ (A.g_ne la i j y hi hj)]
end ReciprocityTheory.L2DbarEstimates.Y
