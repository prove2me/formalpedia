-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.dbar_sectionFrameQuotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:37:20.804922+00:00
-- url     : https://prove2.me/submissions/bcf90fe8-b82a-478c-bac5-449d4b298ce7

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLoc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNull
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ContDiffAtSectionFrameQuotient
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_hyq_sigma_ne
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_isOpen_chart_image_mem
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_hyq_sig_holo
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
    {x : Y} (hx : x ∈ A.Mset w0 s De) (i : ι) (hi : x ∈ (A.chart i).source) (ξ : Fin n → ℂ) :
    A.dbarAt i (fun _ => sectionFrameQuotient A F0 σ) x ξ = A.dbarAt i F0 x ξ / σ i x := by
  have hsh := hyq_sig_holo A hD hσ hx i hi
  have hne := hyq_sigma_ne A hσ hx i hi
  obtain ⟨⟨_, htr⟩, _⟩ := hσ
  obtain ⟨hF0s, hF0t⟩ := hF0
  obtain ⟨ho, hm⟩ := isOpen_chart_image_mem A hD hx i hi
  have hc := (A.chart i).map_source hi
  have hev : sectionFrameQuotient A F0 σ ∘ (A.chart i).symm =ᶠ[𝓝 (A.chart i x)] fun v =>
      (F0 i ∘ (A.chart i).symm) v * ((σ i ∘ (A.chart i).symm) v)⁻¹ := by
    filter_upwards [ho.mem_nhds hm] with v hv
    have hs' := (A.chart i).map_target hv.1
    have hp := A.mem_pick ((A.chart i).symm v)
    simp only [Function.comp_apply, sectionFrameQuotient]
    rw [hF0t i _ _ hs' hp, htr i _ _ hv.2 hs' hp, ← div_eq_mul_inv,
      mul_div_mul_left _ _ (A.g_ne _ i _ _ hs' hp)]
  have hne' : (σ i ∘ (A.chart i).symm) (A.chart i x) ≠ 0 := by
    simpa [(A.chart i).left_inv hi] using hne
  have hFd : DifferentiableAt ℝ (F0 i ∘ (A.chart i).symm) (A.chart i x) :=
    ((hF0s i).contDiffAt ((A.chart i).open_target.mem_nhds hc)).differentiableAt (by simp)
  have hGd : DifferentiableAt ℂ (fun v => ((σ i ∘ (A.chart i).symm) v)⁻¹) (A.chart i x) :=
    hsh.self_of_nhds.inv hne'
  have key : ∀ (j : Fin n) (F G : V n → ℂ) (c : V n), DifferentiableAt ℝ F c →
      DifferentiableAt ℂ G c → wdb n j (fun v => F v * G v) c = wdb n j F c * G c := by
    intro j F G c hF hG
    unfold wdb
    rw [fderiv_fun_mul hF (hG.restrictScalars ℝ), hG.fderiv_restrictScalars ℝ]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      ContinuousLinearMap.coe_restrictScalars', map_smul]
    linear_combination (F c * fderiv ℂ G c (bas n j) / 2) * Complex.I_mul_I
  unfold WeightedAtlas.dbarAt
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  show wdb n j (sectionFrameQuotient A F0 σ ∘ (A.chart i).symm) (A.chart i x) * (starRingEnd ℂ) (ξ j) =
    wdb n j (F0 i ∘ (A.chart i).symm) (A.chart i x) * (starRingEnd ℂ) (ξ j) / σ i x
  have hw1 : wdb n j (sectionFrameQuotient A F0 σ ∘ (A.chart i).symm) (A.chart i x) =
      wdb n j (fun v => (F0 i ∘ (A.chart i).symm) v * ((σ i ∘ (A.chart i).symm) v)⁻¹)
        (A.chart i x) := by
    unfold wdb
    rw [hev.fderiv_eq (𝕜 := ℝ)]
  rw [hw1, key j _ _ _ hFd hGd]
  simp only [Function.comp_apply, (A.chart i).left_inv hi]
  ring
end ReciprocityTheory.L2DbarEstimates.Y
