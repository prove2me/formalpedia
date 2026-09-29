-- Prove2me | solution 1 for StochasticProg.Bounds.thm2_edmundson_madansky_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-27T08:00:00.253191+00:00
-- url     : https://prove2.me/submissions/17ee07f6-da51-4922-80df-dfd951dde6b1

import Mathlib

open MeasureTheory ProbabilityTheory

theorem solution {Ω E α : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {Ξ : Set E} (hΞcompact : IsCompact Ξ)
    {Ext : Type*} [MeasurableSpace Ext] (hExtσ : ∀ A : Set Ext, MeasurableSet A)
    (toE : Ext → E) (hExt : Set.range toE = (convexHull ℝ Ξ).extremePoints ℝ)
    {ξ : Ω → E} (hξrange : ∀ᵐ ω ∂μ, ξ ω ∈ Ξ) (hξint : Integrable ξ μ)
    {D : Set α} {x : α} (hx : x ∈ D) {g : α → E → ℝ}
    (hgconv : ConvexOn ℝ Ξ (g x)) (hgcont : ContinuousOn (g x) Ξ)
    (hgint : Integrable (fun ω => g x (ξ ω)) μ)
    (φ : E → Measure Ext) [∀ e, IsProbabilityMeasure (φ e)]
    (hbary : ∀ e ∈ Ξ, ∫ y : Ext, toE y ∂(φ e) = e)
    (hφmeas : ∀ A : Set Ext, Measurable fun ω => (φ (ξ ω)) A)
    (μExt : Measure Ext) [IsProbabilityMeasure μExt]
    (hμExtdef : ∀ A : Set Ext, μExt A = ∫⁻ ω, (φ (ξ ω)) A ∂μ)
    (hgeint : Integrable (fun y : Ext => g x (toE y)) μExt) :
    ∫ ω, g x (ξ ω) ∂μ ≤ ∫ y : Ext, g x (toE y) ∂μExt := by
  borelize E
  have : DiscreteMeasurableSpace Ext := ⟨hExtσ⟩
  -- extreme points of `co Ξ` lie in `Ξ`
  have hmem : ∀ y, toE y ∈ Ξ := fun y =>
    extremePoints_convexHull_subset (hExt ▸ Set.mem_range_self y)
  -- the Markov kernel `ω ↦ φ (ξ ω)`; eq. (2.6) says `μExt` is its composition with `μ`
  let κ : Kernel Ω Ext := ⟨fun ω => φ (ξ ω),
    Measure.measurable_of_measurable_coe _ fun s _ => hφmeas s⟩
  have hμ : μExt = κ ∘ₘ μ := by
    ext s hs
    rw [hμExtdef, Measure.bind_apply hs κ.aemeasurable]
    rfl
  -- `toE` and `g x ∘ toE` are measurable and bounded on `Ext`
  have htoE_sm : StronglyMeasurable toE :=
    stronglyMeasurable_iff_measurable_separable.2
      ⟨Measurable.of_discrete, hΞcompact.isSeparable.mono (Set.range_subset_iff.2 hmem)⟩
  obtain ⟨C₁, hC₁⟩ := hΞcompact.isBounded.exists_norm_le
  obtain ⟨C₂, hC₂⟩ := hΞcompact.exists_bound_of_continuousOn hgcont
  have hint_toE : ∀ e, Integrable toE (φ e) := fun e =>
    Integrable.of_bound htoE_sm.aestronglyMeasurable C₁ (ae_of_all _ fun y => hC₁ _ (hmem y))
  have hint_h : ∀ e, Integrable (fun y => g x (toE y)) (φ e) := fun e =>
    Integrable.of_bound (Measurable.of_discrete).aestronglyMeasurable C₂
      (ae_of_all _ fun y => hC₂ _ (hmem y))
  -- pointwise Jensen against `φ (ξ ω)`, using the barycenter condition (2.4)
  have hpt : ∀ᵐ ω ∂μ, g x (ξ ω) ≤ ∫ y, g x (toE y) ∂(κ ω) := by
    filter_upwards [hξrange] with ω hω
    have := hgconv.map_integral_le hgcont hΞcompact.isClosed (ae_of_all _ hmem)
      (hint_toE (ξ ω)) (hint_h (ξ ω))
    rw [hbary _ hω] at this
    exact this
  -- integrate over `ω` and use Fubini for the composite measure
  rw [hμ, Measure.comp_eq_comp_const_apply] at hgeint ⊢
  rw [ProbabilityTheory.Kernel.integral_comp hgeint]
  have hI := hgeint.integral_comp
  simp only [Kernel.const_apply] at hI ⊢
  exact integral_mono_ae hgint hI hpt
