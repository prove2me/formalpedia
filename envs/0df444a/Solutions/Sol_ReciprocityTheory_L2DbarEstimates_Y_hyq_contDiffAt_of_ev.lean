-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.hyq_contDiffAt_of_ev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:37:20.836803+00:00
-- url     : https://prove2.me/submissions/155cfd89-c7d8-40e7-a446-e144029d9a3b

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLoc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNull
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ContDiffAtSectionFrameQuotient
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_hyq_contDiffAt_of_holo

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
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {g : V n → ℂ} {c : V n}
    (hg : ∀ᶠ v in 𝓝 c, DifferentiableAt ℂ g v) : ContDiffAt ℝ ∞ g c := by
  obtain ⟨U, hU, hUo, hcU⟩ := _root_.eventually_nhds_iff.1 hg
  exact hyq_contDiffAt_of_holo hUo (fun v hv => (hU v hv).differentiableWithinAt) hcU
end ReciprocityTheory.L2DbarEstimates.Y
