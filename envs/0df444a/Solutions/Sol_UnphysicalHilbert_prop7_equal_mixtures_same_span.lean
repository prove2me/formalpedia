-- Prove2me | solution 1 for UnphysicalHilbert.prop7_equal_mixtures_same_span
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T05:49:28.733021+00:00
-- url     : https://prove2.me/submissions/5c6a74da-2a13-4e6d-828e-9da13be9fe71

import Mathlib
import Definitions.Def_UnphysicalHilbert_StateSpace

open UnphysicalHilbert
open scoped InnerProductSpace

namespace UHMix

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma mixture_apply {ι : Type*} [Fintype ι] (a : ι → ℝ) (ψ : ι → H) (x : H) :
    mixture a ψ x = ∑ i, ((a i : ℂ) * ⟪ψ i, x⟫_ℂ) • ψ i := by
  simp only [mixture, ketBra, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
    innerₛₗ_apply_apply, smul_smul]

lemma mixture_mem_span {ι : Type*} [Fintype ι] (a : ι → ℝ) (ψ : ι → H) (x : H) :
    mixture a ψ x ∈ Submodule.span ℂ (Set.range ψ) := by
  rw [mixture_apply]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

lemma inner_mixture_self {ι : Type*} [Fintype ι] (a : ι → ℝ) (ψ : ι → H) (x : H) :
    ⟪x, mixture a ψ x⟫_ℂ = ((∑ i, a i * ‖⟪ψ i, x⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
  rw [mixture_apply, inner_sum]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_right, ← inner_conj_symm (ψ i) x, mul_assoc, RCLike.conj_mul]
  simp [norm_inner_symm]

lemma eq_zero_of_mixture_eq_zero {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (ψ : ι → H) (w : H) (hw : w ∈ Submodule.span ℂ (Set.range ψ)) (h0 : mixture a ψ w = 0) :
    w = 0 := by
  have h1 := inner_mixture_self a ψ w
  rw [h0, inner_zero_right] at h1
  have h2 : ∑ i, a i * ‖⟪ψ i, w⟫_ℂ‖ ^ 2 = 0 := by exact_mod_cast h1.symm
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by have := ha i; positivity)] at h2
  have h3 : ∀ i, ⟪w, ψ i⟫_ℂ = 0 := by
    intro i
    have := h2 i (Finset.mem_univ i)
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (ha i).ne'
    · rw [← inner_conj_symm]
      have : ⟪ψ i, w⟫_ℂ = 0 := by simpa using h
      simp [this]
  have h4 : Submodule.span ℂ (Set.range ψ) ≤ LinearMap.ker (innerₛₗ ℂ w) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    simp [h3 i]
  have h5 := h4 hw
  simp only [LinearMap.mem_ker, innerₛₗ_apply_apply] at h5
  exact inner_self_eq_zero.mp h5

lemma range_mixture {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 < a i) (ψ : ι → H) :
    LinearMap.range (mixture a ψ) = Submodule.span ℂ (Set.range ψ) := by
  set W := Submodule.span ℂ (Set.range ψ)
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩; exact mixture_mem_span a ψ x
  · intro w hw
    have : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ (Set.finite_range ψ)
    let ρW : W →ₗ[ℂ] W := (mixture a ψ).restrict (fun x _ => mixture_mem_span a ψ x)
    have hinj : Function.Injective ρW := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro x hx
      apply Subtype.ext
      apply eq_zero_of_mixture_eq_zero a ha ψ x x.2
      have := congrArg Subtype.val hx
      simpa [ρW] using this
    obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.mp hinj) ⟨w, hw⟩
    exact ⟨y, by have := congrArg Subtype.val hy; simpa [ρW] using this⟩

end UHMix

open UHMix in
theorem solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ψ : ι → H) (ϕ : κ → H) (hψ : IsNormalizedFamily ψ) (hϕ : IsNormalizedFamily ϕ)
    (a : ι → ℝ) (b : κ → ℝ) (ha : IsStrictConvexWeights a) (hb : IsStrictConvexWeights b)
    (hab : mixture a ψ = mixture b ϕ) :
    Submodule.span ℂ (Set.range ψ) = Submodule.span ℂ (Set.range ϕ) := by
  rw [← range_mixture a ha.1 ψ, ← range_mixture b hb.1 ϕ, hab]
