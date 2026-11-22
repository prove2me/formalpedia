-- Prove2me | solution 1 for VectorValuedHolomorphy.eqOn_of_eqOn_ball
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:08:42.801804+00:00
-- url     : https://prove2.me/submissions/2abe04b6-cbbd-4bb9-93ff-644cc047411d

import Mathlib

open Filter Topology Metric
open scoped Real

set_option autoImplicit false

namespace Sol_VectorValuedHolomorphy_eqOn_of_eqOn_ball

/-- Hahn–Banach: in a Hausdorff locally convex space the continuous linear functionals separate
the points. -/
theorem eq_of_forall_strongDual {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    [PolynormableSpace ℂ E] [T2Space E] {x y : E} (h : ∀ ℓ : StrongDual ℂ E, ℓ x = ℓ y) :
    x = y := by
  have : LocallyConvexSpace ℝ E := (PolynormableSpace.withSeminorms ℂ E).toLocallyConvexSpace
  by_contra hxy
  obtain ⟨ℓ, hℓ⟩ := RCLike.geometric_hahn_banach_point_point (𝕜 := ℂ) hxy
  rw [h ℓ] at hℓ
  exact lt_irrefl _ hℓ

/-- A continuous linear functional composed with a holomorphic vector-valued function is
holomorphic. -/
theorem differentiableOn_strongDual_comp {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    {U : Set ℂ} {f : ℂ → E} (hf : DifferentiableOn ℂ f U) (ℓ : StrongDual ℂ E) :
    DifferentiableOn ℂ (fun z => ℓ (f z)) U := by
  intro z hz
  obtain ⟨f', hf'⟩ := hf z hz
  refine ⟨ℓ.comp f', HasFDerivWithinAt.of_isLittleOTVS ?_⟩
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, map_sub]
    using ℓ.isBigOTVS_comp.trans_isLittleOTVS hf'.isLittleOTVS

/-- A punctured open disc in the complex plane is connected: it is the image of the strip
`(0, ε) × ℝ` under polar coordinates centred at `z`. -/
theorem isPreconnected_ball_diff_singleton (z : ℂ) (ε : ℝ) : IsPreconnected (ball z ε \ {z}) := by
  have himg : ball z ε \ {z} =
      (fun p : ℝ × ℝ => z + (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)) ''
        (Set.Ioo (0 : ℝ) ε ×ˢ (Set.univ : Set ℝ)) := by
    ext w
    constructor
    · rintro ⟨hw, hwz⟩
      have hne : w - z ≠ 0 := sub_ne_zero.2 hwz
      refine ⟨(‖w - z‖, Complex.arg (w - z)), ⟨⟨norm_pos_iff.2 hne, ?_⟩, Set.mem_univ _⟩, ?_⟩
      · simpa [dist_eq_norm] using hw
      · show z + (‖w - z‖ : ℂ) * Complex.exp ((Complex.arg (w - z) : ℂ) * Complex.I) = w
        rw [Complex.norm_mul_exp_arg_mul_I]
        ring
    · rintro ⟨⟨ρ, θ⟩, ⟨⟨hρ0, hρε⟩, -⟩, rfl⟩
      have hnorm : ‖(ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = ρ := by
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
          Real.norm_of_nonneg hρ0.le]
      refine ⟨?_, ?_⟩
      · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, hnorm]
        exact hρε
      · intro hmem
        have h0 : (ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) = 0 := by
          have := Set.mem_singleton_iff.1 hmem
          simpa using this
        rw [h0, norm_zero] at hnorm
        exact hρ0.ne hnorm
  rw [himg]
  refine (isPreconnected_Ioo.prod isPreconnected_univ).image _ (Continuous.continuousOn ?_)
  fun_prop

/-- If two functions with values in a Hausdorff space are continuous at `z` and agree on a
punctured neighbourhood of `z` in `ℂ`, then they agree at `z`. -/
theorem eq_of_eventually_punctured {E : Type*} [TopologicalSpace E] [T2Space E]
    {f₁ f₂ : ℂ → E} {z : ℂ} (h₁ : ContinuousAt f₁ z) (h₂ : ContinuousAt f₂ z)
    (h : ∀ᶠ w in 𝓝[≠] z, f₁ w = f₂ w) : f₁ z = f₂ z :=
  tendsto_nhds_unique_of_eventuallyEq (h₁.tendsto.mono_left nhdsWithin_le_nhds)
    (h₂.tendsto.mono_left nhdsWithin_le_nhds) h

end Sol_VectorValuedHolomorphy_eqOn_of_eqOn_ball

open Sol_VectorValuedHolomorphy_eqOn_of_eqOn_ball in
theorem solution {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    [PolynormableSpace ℂ E] [T2Space E] {Ω D₁ D₂ : Set ℂ} (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hD₁ : ∀ z ∈ Ω, ∀ᶠ w in 𝓝[≠] z, w ∉ D₁) (hD₂ : ∀ z ∈ Ω, ∀ᶠ w in 𝓝[≠] z, w ∉ D₂)
    {f₁ f₂ : ℂ → E} (hf₁ : DifferentiableOn ℂ f₁ (Ω \ D₁))
    (hf₂ : DifferentiableOn ℂ f₂ (Ω \ D₂)) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hB : ball c r ⊆ Ω \ (D₁ ∪ D₂)) (h : Set.EqOn f₁ f₂ (ball c r)) :
    Set.EqOn f₁ f₂ (Ω \ (D₁ ∪ D₂)) := by
  -- `Ω \ Dᵢ` is a neighbourhood of each of its points, hence `fᵢ` is continuous there
  have hnhds : ∀ D : Set ℂ, (∀ z ∈ Ω, ∀ᶠ w in 𝓝[≠] z, w ∉ D) → ∀ z ∈ Ω \ D, Ω \ D ∈ 𝓝 z := by
    intro D hD z hz
    have h1 : ∀ᶠ w in 𝓝 z, w ≠ z → w ∉ D := eventually_nhdsWithin_iff.1 (hD z hz.1)
    filter_upwards [hΩ.mem_nhds hz.1, h1] with w hwΩ hw
    refine ⟨hwΩ, ?_⟩
    rcases eq_or_ne w z with rfl | hwz
    · exact hz.2
    · exact hw hwz
  have hc₁ : ∀ z ∈ Ω \ D₁, ContinuousAt f₁ z := fun z hz =>
    (hf₁.continuousOn z hz).continuousAt (hnhds D₁ hD₁ z hz)
  have hc₂ : ∀ z ∈ Ω \ D₂, ContinuousAt f₂ z := fun z hz =>
    (hf₂.continuousOn z hz).continuousAt (hnhds D₂ hD₂ z hz)
  -- the set `S` of points having a punctured neighbourhood on which `f₁ = f₂`
  set S : Set ℂ := {z | ∀ᶠ w in 𝓝[≠] z, f₁ w = f₂ w} with hSdef
  -- `S` is open
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    have hz' : ∀ᶠ w in 𝓝 z, w ≠ z → f₁ w = f₂ w := eventually_nhdsWithin_iff.1 hz
    filter_upwards [eventually_eventually_nhds.2 hz'] with y hy
    show ∀ᶠ w in 𝓝[≠] y, f₁ w = f₂ w
    rcases eq_or_ne y z with rfl | hyz
    · exact hz
    · rw [eventually_nhdsWithin_iff]
      filter_upwards [hy, isOpen_ne.mem_nhds hyz] with w hw hwz _
      exact hw hwz
  -- `S` contains the centre of the disc
  have hcS : c ∈ S := by
    show ∀ᶠ w in 𝓝[≠] c, f₁ w = f₂ w
    rw [eventually_nhdsWithin_iff]
    filter_upwards [ball_mem_nhds c hr] with w hw _
    exact h hw
  have hcΩ : c ∈ Ω := (hB (mem_ball_self hr)).1
  -- `S` is closed in `Ω`
  have hSclosed : closure S ∩ Ω ⊆ S := by
    rintro z ⟨hzS, hzΩ⟩
    -- a punctured disc `P` around `z` inside `Ω \ (D₁ ∪ D₂)`
    have h1 : ∀ᶠ w in 𝓝 z, w ≠ z → w ∉ D₁ := eventually_nhdsWithin_iff.1 (hD₁ z hzΩ)
    have h2 : ∀ᶠ w in 𝓝 z, w ≠ z → w ∉ D₂ := eventually_nhdsWithin_iff.1 (hD₂ z hzΩ)
    have h0 : ∀ᶠ w in 𝓝 z, w ∈ Ω := hΩ.mem_nhds hzΩ
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (h0.and (h1.and h2))
    have hP₁ : ball z ε \ {z} ⊆ Ω \ D₁ := fun w hw =>
      ⟨(hball w hw.1).1, (hball w hw.1).2.1 hw.2⟩
    have hP₂ : ball z ε \ {z} ⊆ Ω \ D₂ := fun w hw =>
      ⟨(hball w hw.1).1, (hball w hw.1).2.2 hw.2⟩
    have hPopen : IsOpen (ball z ε \ {z}) := isOpen_ball.sdiff isClosed_singleton
    -- a point `z'` of `S` in the disc
    obtain ⟨z', hz'ball, hz'S⟩ := mem_closure_iff_nhds.1 hzS _ (ball_mem_nhds z hε)
    rcases eq_or_ne z' z with rfl | hz'z
    · exact hz'S
    have hz'P : z' ∈ ball z ε \ {z} := ⟨hz'ball, hz'z⟩
    -- `f₁ = f₂` on a full neighbourhood of `z'`
    have hz'eq : f₁ z' = f₂ z' :=
      eq_of_eventually_punctured (hc₁ z' (hP₁ hz'P)) (hc₂ z' (hP₂ hz'P)) hz'S
    have hev : ∀ᶠ w in 𝓝 z', f₁ w = f₂ w := by
      have hz'S' : ∀ᶠ w in 𝓝 z', w ≠ z' → f₁ w = f₂ w := eventually_nhdsWithin_iff.1 hz'S
      filter_upwards [hz'S'] with w hw
      rcases eq_or_ne w z' with rfl | hwz'
      · exact hz'eq
      · exact hw hwz'
    -- scalar identity theorem on the connected punctured disc, for every functional
    have hEq : Set.EqOn f₁ f₂ (ball z ε \ {z}) := by
      intro w hw
      refine eq_of_forall_strongDual fun ℓ => ?_
      have ha₁ : AnalyticOnNhd ℂ (fun u => ℓ (f₁ u)) (ball z ε \ {z}) :=
        ((differentiableOn_strongDual_comp hf₁ ℓ).mono hP₁).analyticOnNhd hPopen
      have ha₂ : AnalyticOnNhd ℂ (fun u => ℓ (f₂ u)) (ball z ε \ {z}) :=
        ((differentiableOn_strongDual_comp hf₂ ℓ).mono hP₂).analyticOnNhd hPopen
      exact ha₁.eqOn_of_preconnected_of_eventuallyEq ha₂
        (isPreconnected_ball_diff_singleton z ε) hz'P
        (hev.mono fun u hu => congrArg ℓ hu) hw
    show ∀ᶠ w in 𝓝[≠] z, f₁ w = f₂ w
    rw [eventually_nhdsWithin_iff]
    filter_upwards [ball_mem_nhds z hε] with w hw hwz
    exact hEq ⟨hw, hwz⟩
  -- connectedness of `Ω`
  have hΩS : Ω ⊆ S := hΩc.subset_of_closure_inter_subset hSopen ⟨c, hcΩ, hcS⟩ hSclosed
  -- conclusion: remove the puncture by continuity
  intro z hz
  have hz₁ : z ∈ Ω \ D₁ := ⟨hz.1, fun hd => hz.2 (Or.inl hd)⟩
  have hz₂ : z ∈ Ω \ D₂ := ⟨hz.1, fun hd => hz.2 (Or.inr hd)⟩
  exact eq_of_eventually_punctured (hc₁ z hz₁) (hc₂ z hz₂) (hΩS hz.1)
