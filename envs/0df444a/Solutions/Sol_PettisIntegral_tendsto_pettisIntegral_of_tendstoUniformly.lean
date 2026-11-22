-- Prove2me | solution 1 for PettisIntegral.tendsto_pettisIntegral_of_tendstoUniformly
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:12:24.328335+00:00
-- url     : https://prove2.me/submissions/e7f53c5c-d736-4cff-949a-17c5ce29fd57

import Mathlib
import Definitions.Def_PettisIntegral_Basic

open MeasureTheory

set_option autoImplicit false

namespace Sol_PettisIntegral_tendsto_pettisIntegral_of_tendstoUniformly

open PettisIntegral

/-- Hahn–Banach: for a continuous seminorm `p` on a polynormable space and a vector `a`, there is
a continuous linear form `φ` with `φ a = p a` and `‖φ x‖ ≤ p x` for all `x`. -/
theorem exists_dual_eq_seminorm {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [PolynormableSpace 𝕜 E] (p : Seminorm 𝕜 E) (hp : Continuous p) (a : E) :
    ∃ φ : StrongDual 𝕜 E, φ a = (p a : 𝕜) ∧ ∀ x, ‖φ x‖ ≤ p x := by
  by_cases ha : a = 0
  · refine ⟨0, ?_, fun x => ?_⟩
    · simp [ha]
    · simp
  · -- the linear form `c • a ↦ c * p a` on the line `𝕜 ∙ a`
    let f : E →ₗ.[𝕜] 𝕜 := LinearPMap.mkSpanSingleton a (p a : 𝕜) ha
    have hdom : ∀ x : f.domain, ‖f.toFun x‖ ≤ p x := by
      rintro ⟨x, hx⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
      have h1 : f.toFun ⟨c • a, hx⟩ = c • (p a : 𝕜) :=
        LinearPMap.mkSpanSingleton'_apply a (p a : 𝕜) _ c hx
      rw [h1]
      simp only [smul_eq_mul, norm_mul, map_smul_eq_mul]
      rw [RCLike.norm_ofReal, abs_of_nonneg (apply_nonneg p a)]
    obtain ⟨g, hg, hgp⟩ :=
      Module.Dual.exists_continuous_extension_of_le_seminorm f.domain f.toFun hp hdom
    refine ⟨g, ?_, hgp⟩
    have hmem : a ∈ f.domain := Submodule.mem_span_singleton_self a
    have h2 := hg ⟨a, hmem⟩
    have h3 : f.toFun ⟨a, hmem⟩ = (p a : 𝕜) :=
      LinearPMap.mkSpanSingleton_apply 𝕜 𝕜 ha (p a : 𝕜)
    rw [← h3]
    exact h2

/-- The value `pettisIntegral 𝕜 μ f` is a Pettis integral of a Pettis integrable function `f`. -/
theorem hasPettisIntegral_pettisIntegral {𝕜 E X : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [MeasurableSpace X] {μ : Measure X} {f : X → E}
    (h : PettisIntegrable 𝕜 μ f) : HasPettisIntegral 𝕜 μ f (pettisIntegral 𝕜 μ f) := by
  unfold pettisIntegral
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- Pettis integrals are additive: a difference of Pettis integrals is a Pettis integral of the
difference. -/
theorem hasPettisIntegral_sub {𝕜 E X : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [MeasurableSpace X] {μ : Measure X} {f g : X → E} {a b : E}
    (ha : HasPettisIntegral 𝕜 μ f a) (hb : HasPettisIntegral 𝕜 μ g b) :
    HasPettisIntegral 𝕜 μ (fun x => f x - g x) (a - b) := by
  refine ⟨fun φ => ?_, fun φ => ?_⟩
  · have h : (fun x => φ (f x - g x)) = fun x => φ (f x) - φ (g x) := by
      funext x
      exact map_sub φ (f x) (g x)
    rw [h]
    exact (ha.1 φ).sub (hb.1 φ)
  · have h : (fun x => φ (f x - g x)) = fun x => φ (f x) - φ (g x) := by
      funext x
      exact map_sub φ (f x) (g x)
    rw [h, integral_sub (ha.1 φ) (hb.1 φ), map_sub, ha.2 φ, hb.2 φ]

/-- If `a` is a Pettis integral of `g` for a finite measure `μ` and a continuous seminorm `p` is
bounded by `C` on the values of `g`, then `p a ≤ C * μ(X)`. -/
theorem seminorm_le_of_forall_le {𝕜 E X : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [PolynormableSpace 𝕜 E] [MeasurableSpace X] {μ : Measure X}
    [IsFiniteMeasure μ] {g : X → E} {a : E} (ha : HasPettisIntegral 𝕜 μ g a)
    (p : Seminorm 𝕜 E) (hp : Continuous p) {C : ℝ} (hC : ∀ x, p (g x) ≤ C) :
    p a ≤ C * μ.real Set.univ := by
  obtain ⟨φ, hφa, hφp⟩ := exists_dual_eq_seminorm p hp a
  have hnorm : p a = ‖∫ x, φ (g x) ∂μ‖ := by
    rw [← ha.2 φ, hφa, RCLike.norm_ofReal, abs_of_nonneg (apply_nonneg p a)]
  rw [hnorm]
  exact norm_integral_le_of_norm_le_const
    (Filter.Eventually.of_forall fun x => (hφp (g x)).trans (hC x))

end Sol_PettisIntegral_tendsto_pettisIntegral_of_tendstoUniformly

open PettisIntegral Sol_PettisIntegral_tendsto_pettisIntegral_of_tendstoUniformly

theorem solution {𝕜 E X ι : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E]
    [PolynormableSpace 𝕜 E] [T2Space E]
    [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [μ.Regular]
    [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (F : ι → X → E) (f : X → E) (hF : ∀ i, Continuous (F i)) (hf : Continuous f)
    (hFi : ∀ i, PettisIntegrable 𝕜 μ (F i)) (hfi : PettisIntegrable 𝕜 μ f)
    (hlim : TendstoUniformly F f Filter.atTop) :
    Filter.Tendsto (fun i => pettisIntegral 𝕜 μ (F i)) Filter.atTop
      (nhds (pettisIntegral 𝕜 μ f)) := by
  have _ := hF
  have _ := hf
  rw [(PolynormableSpace.withSeminorms 𝕜 E).tendsto_nhds]
  rintro ⟨p, hp⟩ ε hε
  change ∀ᶠ i in Filter.atTop, p (pettisIntegral 𝕜 μ (F i) - pettisIntegral 𝕜 μ f) < ε
  -- choose `δ > 0` with `δ * μ(X) < ε`
  have hM : 0 ≤ μ.real Set.univ := measureReal_nonneg
  obtain ⟨δ, hδ, hδM⟩ : ∃ δ : ℝ, 0 < δ ∧ δ * μ.real Set.univ < ε := by
    refine ⟨ε / (μ.real Set.univ + 1), by positivity, ?_⟩
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  -- the entourage `{(u, v) | p (u - v) < δ}` of the uniform structure of `E`
  have hU : {q : E × E | p (q.1 - q.2) < δ} ∈ uniformity E := by
    rw [uniformity_eq_comap_nhds_zero E]
    refine ⟨{u : E | p u < δ}, ?_, ?_⟩
    · exact (isOpen_lt hp continuous_const).mem_nhds (by simpa using hδ)
    · rintro ⟨u, v⟩ h
      have h' : p (v - u) < δ := h
      change p (u - v) < δ
      rwa [← map_neg_eq_map, neg_sub]
  filter_upwards [hlim _ hU] with i hi
  have hsub := hasPettisIntegral_sub (hasPettisIntegral_pettisIntegral (hFi i))
    (hasPettisIntegral_pettisIntegral hfi)
  have hb : p (pettisIntegral 𝕜 μ (F i) - pettisIntegral 𝕜 μ f) ≤ δ * μ.real Set.univ :=
    seminorm_le_of_forall_le hsub p hp fun x => by
      have h : p (f x - F i x) < δ := hi x
      rw [← map_neg_eq_map, neg_sub]
      exact h.le
  exact lt_of_le_of_lt hb hδM
