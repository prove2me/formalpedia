-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.leviAt_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:12:39.788261+00:00
-- url     : https://prove2.me/submissions/7682aa2d-c2ec-4474-a0b1-db5d73a82942

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLocA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLoc
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_leviV_congr


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
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) (i : ι) (f g : Y → ℝ) (y : Y) (hy : y ∈ (A.chart i).source)
    (h : f =ᶠ[𝓝 y] g) (ξ : Fin n → ℂ) : A.leviAt i f y ξ = A.leviAt i g y ξ := by

  unfold WeightedAtlas.leviAt
  congr 1
  apply leviV_congr
  have hc := (A.chart i).continuousAt_symm ((A.chart i).map_source hy)
  rw [ContinuousAt, (A.chart i).left_inv hy] at hc
  filter_upwards [hc.eventually h] with v hv
  simp only [hv]
end ReciprocityTheory.L2DbarEstimates.Y
