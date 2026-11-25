-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.hyq_sigma_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:20:42.795997+00:00
-- url     : https://prove2.me/submissions/3e0a2c8a-1670-4ec5-ac9d-943ce7318020

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLoc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNull
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ContDiffAtSectionFrameQuotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas Metric
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
variable   (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} {la : La} {σ : ι → Y → ℂ}
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (hσ : A.IsFrameOn (A.kap + la) (A.Mset w0 s De) σ) {y : Y}
    (hy : y ∈ A.Mset w0 s De) (i : ι) (hi : y ∈ (A.chart i).source) : σ i y ≠ 0 := by
  obtain ⟨⟨_, htr⟩, hne⟩ := hσ
  rw [htr i (A.pick y) y hy hi (A.mem_pick y)]
  exact mul_ne_zero (A.g_ne _ i (A.pick y) y hi (A.mem_pick y)) (hne y hy)
end ReciprocityTheory.L2DbarEstimates.Y
