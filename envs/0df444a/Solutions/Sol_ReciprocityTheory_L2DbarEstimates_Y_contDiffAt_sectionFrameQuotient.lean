-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.contDiffAt_sectionFrameQuotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:08:11.634483+00:00
-- url     : https://prove2.me/submissions/32ae96d5-1e44-45ea-a414-ed023c6d5427

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLoc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNull
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ContDiffAtSectionFrameQuotient
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_hyq_sigma_ne
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_isOpen_chart_image_mem
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_hyq_sig_cd
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fn_hom_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.L2DbarEstimates.Y.fn_hom_zero



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
    {F0 : ι → Y → ℂ} (hF0 : A.IsSSec (A.kap + la) F0)
    {x : Y} (hx : x ∈ A.Mset w0 s De) (i : ι) (hi : x ∈ (A.chart i).source) :
    ContDiffAt ℝ ∞ (sectionFrameQuotient A F0 σ ∘ (A.chart i).symm) (A.chart i x) := by
  have h2 := hyq_sig_cd A hD hσ hx i hi
  have hne := hyq_sigma_ne A hσ hx i hi
  obtain ⟨⟨_, htr⟩, _⟩ := hσ
  obtain ⟨hF0s, hF0t⟩ := hF0
  obtain ⟨ho, hm⟩ := isOpen_chart_image_mem A hD hx i hi
  have hev : sectionFrameQuotient A F0 σ ∘ (A.chart i).symm =ᶠ[𝓝 (A.chart i x)] fun v =>
      F0 i ((A.chart i).symm v) / σ i ((A.chart i).symm v) := by
    filter_upwards [ho.mem_nhds hm] with v hv
    have hs' := (A.chart i).map_target hv.1
    have hp := A.mem_pick ((A.chart i).symm v)
    simp only [Function.comp_apply, sectionFrameQuotient]
    rw [hF0t i _ _ hs' hp, htr i _ _ hv.2 hs' hp,
      mul_div_mul_left _ _ (A.g_ne _ i _ _ hs' hp)]
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  have h1 : ContDiffAt ℝ ∞ (F0 i ∘ (A.chart i).symm) (A.chart i x) :=
    (hF0s i).contDiffAt ((A.chart i).open_target.mem_nhds ((A.chart i).map_source hi))
  have hne' : (σ i ∘ (A.chart i).symm) (A.chart i x) ≠ 0 := by
    simpa [(A.chart i).left_inv hi] using hne
  have h3 := h1.mul (h2.inv hne')
  refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun v => ?_)
  simp [div_eq_mul_inv]
end ReciprocityTheory.L2DbarEstimates.Y
