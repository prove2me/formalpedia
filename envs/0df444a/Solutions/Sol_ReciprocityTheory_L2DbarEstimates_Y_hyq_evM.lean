-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.hyq_evM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:30:55.269582+00:00
-- url     : https://prove2.me/submissions/0ccecc73-0006-4d40-9c53-ddb718285dda

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLoc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNull
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ContDiffAtSectionFrameQuotient
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_isOpen_chart_image_mem

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
theorem _root_.solution (hD : A.D0 L w w0 s) {x : Y} (hx : x ∈ A.Mset w0 s De) (i : ι)
    (hi : x ∈ (A.chart i).source) :
    ∀ᶠ v in 𝓝 (A.chart i x), v ∈ (A.chart i).target ∧ (A.chart i).symm v ∈ A.Mset w0 s De := by
  obtain ⟨ho, hm⟩ := isOpen_chart_image_mem A hD hx i hi
  filter_upwards [ho.mem_nhds hm] with v hv
  exact ⟨hv.1, hv.2⟩
end ReciprocityTheory.L2DbarEstimates.Y
