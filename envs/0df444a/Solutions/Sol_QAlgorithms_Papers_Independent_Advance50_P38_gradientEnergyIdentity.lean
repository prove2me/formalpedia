-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P38.gradientEnergyIdentity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T11:25:56.808966+00:00
-- url     : https://prove2.me/submissions/c43fa3af-8601-4bed-9458-ed76d75f84be

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P38
namespace QAlgorithms.Papers.Independent.Advance50.P38

open scoped BigOperators Topology Manifold ContDiff

end QAlgorithms.Papers.Independent.Advance50.P38

open QAlgorithms.Papers.Independent.Advance50.P38
open scoped BigOperators Topology Manifold ContDiff

noncomputable section

theorem s109_21_rep {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hpos : ∀ v, v ≠ 0 → 0 < B v v) (L : V →L[ℝ] ℝ) :
    ∀ w, B (metricRepresentative (fun v w => B v w) (fun w => L w)) w = L w := by
  classical
  let Φ : V →ₗ[ℝ] Module.Dual ℝ V :=
    { toFun := fun v => (B v).toLinearMap
      map_add' := fun v w => by ext u; simp
      map_smul' := fun c v => by ext u; simp }
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    by_contra hne
    have h1 := hpos v hne
    have h2 : B v v = 0 := by
      have := LinearMap.congr_fun hv v
      simpa [Φ] using this
    linarith
  have hsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq).symm).mp hinj
  obtain ⟨v, hv⟩ := hsurj L.toLinearMap
  have hex : ∃ v, ∀ w, (fun v w => B v w) v w = (fun w => L w) w :=
    ⟨v, fun w => by simpa [Φ] using LinearMap.congr_fun hv w⟩
  intro w
  unfold metricRepresentative
  rw [dif_pos hex]
  exact Classical.choose_spec hex w

theorem solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [SecondCountableTopology M]
    (g : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (fun x : M => TangentSpace 𝓘(ℝ, E) x))
    (f : M → ℝ) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) :
    (∀ x (v : TangentSpace 𝓘(ℝ, E) x),
      g.inner x (riemannianGradient g f x) v = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x v) ∧
    (∀ x, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x = 0 ↔ riemannianGradient g f x = 0) ∧
    ∀ (s : Set ℝ), IsOpen s → Convex ℝ s → ∀ gamma : ℝ → M,
      ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ gamma s →
      (∀ t ∈ s, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) gamma t (1 : ℝ) =
        riemannianGradient g f (gamma t)) →
      (∀ t ∈ s,
        HasDerivAt (fun u => f (gamma u))
          (g.inner (gamma t) (riemannianGradient g f (gamma t))
            (riemannianGradient g f (gamma t))) t ∧
        0 ≤ g.inner (gamma t) (riemannianGradient g f (gamma t))
          (riemannianGradient g f (gamma t))) ∧
      MonotoneOn (fun t => f (gamma t)) s := by
  have h1 : ∀ x (v : TangentSpace 𝓘(ℝ, E) x),
      g.inner x (riemannianGradient g f x) v = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x v := by
    intro x v
    exact s109_21_rep (V := E) (g.inner x) (g.pos x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x) v
  have hnn : ∀ x (v : TangentSpace 𝓘(ℝ, E) x), 0 ≤ g.inner x v v := by
    intro x v
    by_cases hv : v = 0
    · subst hv; simp
    · exact (g.pos x v hv).le
  refine ⟨h1, ?_, ?_⟩
  · intro x
    constructor
    · intro h0
      by_contra hne
      have := g.pos x _ hne
      rw [h1, h0, ContinuousLinearMap.zero_apply] at this
      exact lt_irrefl (0 : ℝ) this
    · intro h0
      ext v
      rw [← h1, h0, map_zero, ContinuousLinearMap.zero_apply]
      rfl
  · intro s hs hconv gamma hgam hgrad
    have hD : ∀ t ∈ s, HasDerivAt (fun u => f (gamma u))
        (g.inner (gamma t) (riemannianGradient g f (gamma t))
          (riemannianGradient g f (gamma t))) t := by
      intro t ht
      have hga : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) gamma t :=
        ((hgam t ht).contMDiffAt (hs.mem_nhds ht)).mdifferentiableAt (by simp)
      have hfa : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f (gamma t) :=
        (hf (gamma t)).mdifferentiableAt (by simp)
      have hc := hfa.hasMFDerivAt.comp t hga.hasMFDerivAt
      let L' : ℝ →L[ℝ] ℝ := (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f (gamma t)).comp
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) gamma t)
      have hF : HasFDerivAt (fun u => f (gamma u)) L' t := hc.hasFDerivAt
      have hval : L' 1 = g.inner (gamma t) (riemannianGradient g f (gamma t))
          (riemannianGradient g f (gamma t)) := by
        have e := congrArg (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f (gamma t)) (hgrad t ht)
        exact e.trans (h1 _ _).symm
      rw [← hval]
      exact hF.hasDerivAt
    refine ⟨fun t ht => ⟨hD t ht, hnn _ _⟩, ?_⟩
    refine monotoneOn_of_deriv_nonneg hconv ?_ ?_ ?_
    · exact fun t ht => (hD t ht).continuousAt.continuousWithinAt
    · rw [hs.interior_eq]
      exact fun t ht => (hD t ht).differentiableAt.differentiableWithinAt
    · rw [hs.interior_eq]
      intro t ht
      rw [(hD t ht).deriv]
      exact hnn _ _

end
