-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.flL_zLoc_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:13:59.500113+00:00
-- url     : https://prove2.me/submissions/25294bd5-788c-4ccb-95c3-0f7d0ffbe3ec

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLocA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLoc
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
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ}
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (hD : A.D0 L w w0 s) {y : Y} {i : ι} (hi : y ∈ (A.chart i).source)
    (_hne : w0 i y ≠ 0) : A.zLoc w0 s i (A.chart i y) = A.zmap w0 s y := by

  have hp := A.mem_pick y
  unfold WeightedAtlas.zLoc WeightedAtlas.zmap
  rw [(A.chart i).left_inv hi]
  congr 1
  funext k
  have hw := hD.isSection_denom
  have hs := hD.sec_s k
  unfold WeightedAtlas.IsSec WeightedAtlas.IsSecOn at hw hs
  rw [hw.2 i (A.pick y) y trivial hi hp, hs.2 i (A.pick y) y trivial hi hp]
  exact mul_div_mul_left _ _ (A.g_ne L i (A.pick y) y hi hp)
end ReciprocityTheory.L2DbarEstimates.Y
