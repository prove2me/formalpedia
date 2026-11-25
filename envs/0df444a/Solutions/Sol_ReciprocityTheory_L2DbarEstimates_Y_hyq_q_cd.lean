-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.hyq_q_cd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:22:57.61749+00:00
-- url     : https://prove2.me/submissions/d48615f4-de59-46c5-88e3-b8a943e62e07

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLoc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNull
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ContDiffAtSectionFrameQuotient
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_hyq_sigma_ne
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_hyq_sig_holo
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_hyq_evM
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_differentiableAt_det_jz
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fn_hom_zero
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_jz_det_ne
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
theorem _root_.solution (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn (A.kap + la) (A.Mset w0 s De) σ)
    {x : Y} (hx : x ∈ A.Mset w0 s De) (i : ι) (hi : x ∈ (A.chart i).source) :
    (∀ᶠ v in 𝓝 (A.chart i x), DifferentiableAt ℂ
      (fun v => (fderiv ℂ (A.zLoc w0 s i) v).det * (σ i ((A.chart i).symm v))⁻¹) v) ∧
    ((fun y => (jz A w0 s i y).det * (σ i y)⁻¹) ∘ (A.chart i).symm =ᶠ[𝓝 (A.chart i x)]
      fun v => (fderiv ℂ (A.zLoc w0 s i) v).det * (σ i ((A.chart i).symm v))⁻¹) ∧
    (fun v => (fderiv ℂ (A.zLoc w0 s i) v).det * (σ i ((A.chart i).symm v))⁻¹) (A.chart i x) ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [differentiableAt_det_jz A hD hF x hx i hi, hyq_sig_holo A hD hσ hx i hi,
      hyq_evM A hD hx i hi] with v h1 h2 h3
    exact h1.mul (h2.inv (hyq_sigma_ne A hσ h3.2 i ((A.chart i).map_target h3.1)))
  · filter_upwards [(A.chart i).open_target.mem_nhds ((A.chart i).map_source hi)] with v hv
    simp only [Function.comp, jz, (A.chart i).right_inv hv]
  · simp only [(A.chart i).left_inv hi]
    exact mul_ne_zero (by simpa [jz] using jz_det_ne A hD hF x hx i hi)
      (inv_ne_zero (hyq_sigma_ne A hσ hx i hi))
end ReciprocityTheory.L2DbarEstimates.Y
