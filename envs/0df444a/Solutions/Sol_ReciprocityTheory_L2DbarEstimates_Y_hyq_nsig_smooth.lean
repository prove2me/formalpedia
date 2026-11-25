-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.hyq_nsig_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:02:22.340277+00:00
-- url     : https://prove2.me/submissions/8ecd6b79-626f-42d6-8b9b-58d1aec5237c

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLoc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNull
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ContDiffAtSectionFrameQuotient
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_hyq_nsq_chart
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_isOpen_chart_image_mem
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_hyq_sig_cd

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
theorem _root_.solution (hD : A.D0 L w w0 s) (hσ : A.IsFrameOn (A.kap + la) (A.Mset w0 s De) σ)
    {x : Y} (hx : x ∈ A.Mset w0 s De) (i : ι) (hi : x ∈ (A.chart i).source) :
    ContDiffAt ℝ ∞ (A.nsq (A.kap + la) σ ∘ (A.chart i).symm) (A.chart i x) := by
  have hsg := hyq_sig_cd A hD hσ hx i hi
  obtain ⟨⟨_, htr⟩, _⟩ := hσ
  obtain ⟨ho, hm⟩ := isOpen_chart_image_mem A hD hx i hi
  have hev : A.nsq (A.kap + la) σ ∘ (A.chart i).symm =ᶠ[𝓝 (A.chart i x)] fun v =>
      ‖σ i ((A.chart i).symm v)‖ ^ 2 * Real.exp (-A.ph (A.kap + la) i ((A.chart i).symm v)) := by
    filter_upwards [ho.mem_nhds hm] with v hv
    have hs' := (A.chart i).map_target hv.1
    exact hyq_nsq_chart A (A.kap + la) σ i ((A.chart i).symm v) hs'
      (htr i (A.pick ((A.chart i).symm v)) ((A.chart i).symm v) hv.2 hs' (A.mem_pick _))
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  have hph : ContDiffAt ℝ ∞ (A.ph (A.kap + la) i ∘ (A.chart i).symm) (A.chart i x) :=
    (A.smooth_ph (A.kap + la) i).contDiffAt
      ((A.chart i).open_target.mem_nhds ((A.chart i).map_source hi))
  exact (hsg.norm_sq ℝ).mul hph.neg.exp
end ReciprocityTheory.L2DbarEstimates.Y
