-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.denominator_ne_zero_on_set
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:41:24.985893+00:00
-- url     : https://prove2.me/submissions/8f792884-981b-45cf-a0d4-358f313fdbff

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalcA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ContinuousOnSec
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalcB

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
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s) {y : Y}
    (hy : y ∈ A.Mset w0 s De) (i : ι) (hi : y ∈ (A.chart i).source) : w0 i y ≠ 0 := by
  have secW : ∀ i j y, y ∈ (A.chart i).source → y ∈ (A.chart j).source →
      w0 i y = A.g L i j y * w0 j y := by
    intro i j y hi hj
    have hs := hD.isSection_denom
    unfold WeightedAtlas.IsSec WeightedAtlas.IsSecOn at hs
    exact hs.2 i j y trivial hi hj
  rw [secW i (A.pick y) y hi (A.mem_pick y)]
  exact mul_ne_zero (A.g_ne L i (A.pick y) y hi (A.mem_pick y)) hy.1
end ReciprocityTheory.L2DbarEstimates.Y
