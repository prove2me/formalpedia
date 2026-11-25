-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.hyq_levi_phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:47:23.347341+00:00
-- url     : https://prove2.me/submissions/5c76390a-1bff-48fd-8a70-10e8140b4e12

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLoc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNull
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ContDiffAtSectionFrameQuotient
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_hyq_sigma_ne
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_hyq_sig_cd
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_hyq_phi_loc
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_hyq_q_cd
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_contDiffAt_det_jz
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fn_hom_zero
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_jz_det_ne
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_leviAt_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_leviAt_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_leviAt_log_normSq
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
    {x : Y} (hx : x ∈ A.Mset w0 s De) (i : ι) (hi : x ∈ (A.chart i).source) (ξ : Fin n → ℂ) :
    A.leviAt i (hyPhi A w0 s σ la ps) x ξ = A.leviAt i (fun y => A.ph la i y + ps y) x ξ := by
  obtain ⟨hqd, hqe, hqne⟩ := hyq_q_cd A hD hF hσ hx i hi
  have hc : (A.chart i).symm (A.chart i x) = x := (A.chart i).left_inv hi
  have hT := (A.chart i).open_target.mem_nhds ((A.chart i).map_source hi)
  have hq : ContDiffAt ℝ ∞ (fun v => (fderiv ℂ (A.zLoc w0 s i) v).det *
      (σ i ((A.chart i).symm v))⁻¹) (A.chart i x) :=
    ((contDiffAt_det_jz A hD hF x hx i hi).restrict_scalars ℝ).mul
      ((hyq_sig_cd A hD hσ hx i hi).inv (by simp only [Function.comp, hc]; exact hyq_sigma_ne A hσ hx i hi))
  have hf2 : ContDiffAt ℝ 2 ((fun y => A.ph la i y + ps y) ∘ (A.chart i).symm) (A.chart i x) :=
    (((A.smooth_ph la i).contDiffAt hT).add ((hps i).contDiffAt hT)).of_le (WithTop.coe_le_coe.mpr le_top)
  have hg2 : ContDiffAt ℝ 2 ((fun y => Real.log (‖(jz A w0 s i y).det * (σ i y)⁻¹‖ ^ 2)) ∘
      (A.chart i).symm) (A.chart i x) := by
    refine (((hq.norm_sq ℝ).log (by positivity)).of_le (WithTop.coe_le_coe.mpr le_top)).congr_of_eventuallyEq ?_
    filter_upwards [hqe] with v hv
    simp only [Function.comp] at hv ⊢
    rw [hv]
  have hh : ∀ᶠ v in 𝓝 (A.chart i x), DifferentiableAt ℂ
      ((fun y => (jz A w0 s i y).det * (σ i y)⁻¹) ∘ (A.chart i).symm) v := by
    filter_upwards [hqd, hqe.eventuallyEq_nhds] with v h1 h2
    exact h1.congr_of_eventuallyEq h2
  rw [leviAt_congr A i _ _ x hi (hyq_phi_loc A hD hF hσ ps hx i hi) ξ,
    leviAt_add A i (fun y => A.ph la i y + ps y)
      (fun y => Real.log (‖(jz A w0 s i y).det * (σ i y)⁻¹‖ ^ 2)) x hf2 hg2 ξ,
    leviAt_log_normSq A i (fun y => (jz A w0 s i y).det * (σ i y)⁻¹) x hi hh
      (mul_ne_zero (jz_det_ne A hD hF x hx i hi) (inv_ne_zero (hyq_sigma_ne A hσ hx i hi))) ξ,
    add_zero]
end ReciprocityTheory.L2DbarEstimates.Y
