-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.denominator_ne_zero_on_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:16:11.967916+00:00
-- url     : https://prove2.me/submissions/b947342c-f917-4896-bde9-3215e49ec891

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
theorem _root_.solution (hD : A.D0 L w w0 s) {x : Y} (hx : x ∈ A.Mset w0 s De) {i : ι}
    (hi : x ∈ (A.chart i).source) : w0 i x ≠ 0 := by

  have hw := hD.isSection_denom
  unfold WeightedAtlas.IsSec WeightedAtlas.IsSecOn at hw
  rw [hw.2 i (A.pick x) x trivial hi (A.mem_pick x)]
  exact mul_ne_zero (A.g_ne L i (A.pick x) x hi (A.mem_pick x)) hx.1
end ReciprocityTheory.L2DbarEstimates.Y
