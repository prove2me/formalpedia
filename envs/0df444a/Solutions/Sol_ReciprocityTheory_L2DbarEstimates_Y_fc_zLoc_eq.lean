-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.fc_zLoc_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:40:45.452771+00:00
-- url     : https://prove2.me/submissions/657ad780-92fd-491a-86ca-a7e28d1af473

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalcA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ContinuousOnSec
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalcB
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
open scoped ContDiff ENNReal
noncomputable section
universe u
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} (hD : A.D0 L w w0 s) (i : ι) (v : V n)
    (hv : v ∈ (A.chart i).target) :
    A.zLoc w0 s i v = A.zmap w0 s ((A.chart i).symm v) := by
  have secS : ∀ k i j y, y ∈ (A.chart i).source → y ∈ (A.chart j).source →
      s k i y = A.g L i j y * s k j y := by
    intro k i j y hi hj
    have hs := hD.sec_s k
    unfold WeightedAtlas.IsSec WeightedAtlas.IsSecOn at hs
    exact hs.2 i j y trivial hi hj
  have secW : ∀ i j y, y ∈ (A.chart i).source → y ∈ (A.chart j).source →
      w0 i y = A.g L i j y * w0 j y := by
    intro i j y hi hj
    have hs := hD.isSection_denom
    unfold WeightedAtlas.IsSec WeightedAtlas.IsSecOn at hs
    exact hs.2 i j y trivial hi hj
  have hy : (A.chart i).symm v ∈ (A.chart i).source := (A.chart i).map_target hv
  unfold WeightedAtlas.zLoc WeightedAtlas.zmap
  congr 1
  funext k
  rw [secS k i (A.pick _) _ hy (A.mem_pick _), secW i (A.pick _) _ hy (A.mem_pick _),
    mul_div_mul_left _ _ (A.g_ne L i (A.pick _) _ hy (A.mem_pick _))]
end ReciprocityTheory.L2DbarEstimates.Y
