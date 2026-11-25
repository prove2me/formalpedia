-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.hyq_phi_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:47:25.698057+00:00
-- url     : https://prove2.me/submissions/f97d7d66-986f-4520-bd8f-4b6a6bb4951f

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLoc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNull
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ContDiffAtSectionFrameQuotient
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_hyq_contDiffAt_of_ev
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_hyq_phi_loc
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_hyq_q_cd
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
theorem _root_.solution (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn (A.kap + la) (A.Mset w0 s De) σ) {ps : Y → ℝ} (hps : A.SmoothFn ps)
    {x : Y} (hx : x ∈ A.Mset w0 s De) (i : ι) (hi : x ∈ (A.chart i).source) :
    ContDiffAt ℝ ∞ (hyPhi A w0 s σ la ps ∘ (A.chart i).symm) (A.chart i x) := by
  have hloc := hyq_phi_loc A hD hF hσ ps hx i hi
  obtain ⟨hQd, hQeq, hQne⟩ := hyq_q_cd A hD hF hσ hx i hi
  have hc := (A.chart i).map_source hi
  have ht : Filter.Tendsto (A.chart i).symm (𝓝 (A.chart i x)) (𝓝 x) := by
    have h0 := (A.chart i).continuousAt_symm hc
    rwa [ContinuousAt, (A.chart i).left_inv hi] at h0
  have h1 : hyPhi A w0 s σ la ps ∘ (A.chart i).symm =ᶠ[𝓝 (A.chart i x)] fun v =>
      (A.ph la i ((A.chart i).symm v) + ps ((A.chart i).symm v)) +
        Real.log (‖(fderiv ℂ (A.zLoc w0 s i) v).det * (σ i ((A.chart i).symm v))⁻¹‖ ^ 2) := by
    filter_upwards [hloc.comp_tendsto ht, hQeq] with v e1 e2
    simp only [Function.comp_apply] at e1 e2 ⊢
    rw [e1, e2]
  refine ContDiffAt.congr_of_eventuallyEq ?_ h1
  have hph : ContDiffAt ℝ ∞ (A.ph la i ∘ (A.chart i).symm) (A.chart i x) :=
    (A.smooth_ph la i).contDiffAt ((A.chart i).open_target.mem_nhds hc)
  have hps' : ContDiffAt ℝ ∞ (ps ∘ (A.chart i).symm) (A.chart i x) :=
    (hps i).contDiffAt ((A.chart i).open_target.mem_nhds hc)
  have hQs := hyq_contDiffAt_of_ev hQd
  have hlog := (hQs.norm_sq ℝ).log (pow_ne_zero 2 (norm_ne_zero_iff.2 hQne))
  exact (hph.add hps').add hlog
end ReciprocityTheory.L2DbarEstimates.Y
