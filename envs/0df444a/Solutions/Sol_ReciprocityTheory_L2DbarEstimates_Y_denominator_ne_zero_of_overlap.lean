-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.denominator_ne_zero_of_overlap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:31:46.694802+00:00
-- url     : https://prove2.me/submissions/72efd7ae-4132-46f1-b2fd-6a908f73d606

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLocA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLoc

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
universe u
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ}
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (hD : A.D0 L w w0 s) {y : Y} {i j : ι} (hi : y ∈ (A.chart i).source)
    (hj : y ∈ (A.chart j).source) (h : w0 j y ≠ 0) : w0 i y ≠ 0 := by

  have hw := hD.isSection_denom
  unfold WeightedAtlas.IsSec WeightedAtlas.IsSecOn at hw
  rw [hw.2 i j y trivial hi hj]
  exact mul_ne_zero (A.g_ne L i j y hi hj) h
end ReciprocityTheory.L2DbarEstimates.Y
