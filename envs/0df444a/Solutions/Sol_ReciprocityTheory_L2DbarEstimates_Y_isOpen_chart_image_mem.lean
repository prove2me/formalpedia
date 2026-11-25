-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.isOpen_chart_image_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:20:43.935745+00:00
-- url     : https://prove2.me/submissions/5fb86a30-7089-48b3-9f0d-06359ae38c01

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLoc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNull
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ContDiffAtSectionFrameQuotient
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono
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
theorem _root_.solution (hD : A.D0 L w w0 s) {x : Y} (hx : x ∈ A.Mset w0 s De) (i : ι)
    (hi : x ∈ (A.chart i).source) :
    IsOpen ((A.chart i).target ∩ (A.chart i).symm ⁻¹' A.Mset w0 s De) ∧
      A.chart i x ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' A.Mset w0 s De := by
  obtain ⟨hw0d, hw0t⟩ := hD.isSection_denom
  have hsd : ∀ k, DifferentiableOn ℂ (s k i ∘ (A.chart i).symm)
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' Set.univ) := fun k => by
    obtain ⟨h1, _⟩ := hD.sec_s k
    exact h1 i
  have hst : ∀ k, ∀ i j y, y ∈ (Set.univ : Set Y) → y ∈ (A.chart i).source →
      y ∈ (A.chart j).source → s k i y = A.g L i j y * s k j y := fun k => by
    obtain ⟨_, h2⟩ := hD.sec_s k
    exact h2
  have hT : (A.chart i).target ∩ (A.chart i).symm ⁻¹' Set.univ = (A.chart i).target := by simp
  have hw0c : ContinuousOn (w0 i ∘ (A.chart i).symm) (A.chart i).target := by
    have h := (hw0d i).continuousOn
    rwa [hT] at h
  have hsc : ∀ k, ContinuousOn (s k i ∘ (A.chart i).symm) (A.chart i).target := fun k => by
    have h := (hsd k).continuousOn
    rwa [hT] at h
  have hU1 : IsOpen ((A.chart i).target ∩ (w0 i ∘ (A.chart i).symm) ⁻¹' {0}ᶜ) :=
    hw0c.isOpen_inter_preimage (A.chart i).open_target isOpen_compl_singleton
  have hF2 : ContinuousOn (fun v => MvPolynomial.eval
      (fun k => s k i ((A.chart i).symm v) / w0 i ((A.chart i).symm v)) De)
      ((A.chart i).target ∩ (w0 i ∘ (A.chart i).symm) ⁻¹' {0}ᶜ) :=
    (MvPolynomial.continuous_eval De).comp_continuousOn (continuousOn_pi.2 fun k =>
      ((hsc k).mono Set.inter_subset_left).div (hw0c.mono Set.inter_subset_left)
        (fun v hv => hv.2))
  have hU2 := hF2.isOpen_inter_preimage hU1 (isOpen_compl_singleton (x := (0 : ℂ)))
  have key : ∀ v ∈ (A.chart i).target, ((A.chart i).symm v ∈ A.Mset w0 s De ↔
      (w0 i ((A.chart i).symm v) ≠ 0 ∧ MvPolynomial.eval
        (fun k => s k i ((A.chart i).symm v) / w0 i ((A.chart i).symm v)) De ≠ 0)) := by
    intro v hv
    have hy : (A.chart i).symm v ∈ (A.chart i).source := (A.chart i).map_target hv
    have hp := A.mem_pick ((A.chart i).symm v)
    have hg := A.g_ne L i (A.pick ((A.chart i).symm v)) ((A.chart i).symm v) hy hp
    have e0 := hw0t i (A.pick ((A.chart i).symm v)) ((A.chart i).symm v) (Set.mem_univ _) hy hp
    have ek : ∀ k, s k i ((A.chart i).symm v) / w0 i ((A.chart i).symm v) =
        s k (A.pick ((A.chart i).symm v)) ((A.chart i).symm v) /
          w0 (A.pick ((A.chart i).symm v)) ((A.chart i).symm v) := fun k => by
      rw [hst k i (A.pick ((A.chart i).symm v)) ((A.chart i).symm v) (Set.mem_univ _) hy hp, e0,
        mul_div_mul_left _ _ hg]
    simp only [ek]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · rw [e0]
        exact mul_ne_zero hg h1
      · simpa [WeightedAtlas.zmap] using h2
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · intro h0
        apply h1
        rw [e0, h0, mul_zero]
      · simpa [WeightedAtlas.zmap] using h2
  have hW : (A.chart i).target ∩ (A.chart i).symm ⁻¹' A.Mset w0 s De =
      ((A.chart i).target ∩ (w0 i ∘ (A.chart i).symm) ⁻¹' {0}ᶜ) ∩ (fun v => MvPolynomial.eval
        (fun k => s k i ((A.chart i).symm v) / w0 i ((A.chart i).symm v)) De) ⁻¹' {0}ᶜ := by
    ext v
    constructor
    · rintro ⟨hv, hm⟩
      exact ⟨⟨hv, ((key v hv).1 hm).1⟩, ((key v hv).1 hm).2⟩
    · rintro ⟨⟨hv, h1⟩, h2⟩
      exact ⟨hv, (key v hv).2 ⟨h1, h2⟩⟩
  refine ⟨by rw [hW]; exact hU2, (A.chart i).map_source hi, ?_⟩
  rw [Set.mem_preimage, (A.chart i).left_inv hi]
  exact hx
end ReciprocityTheory.L2DbarEstimates.Y
