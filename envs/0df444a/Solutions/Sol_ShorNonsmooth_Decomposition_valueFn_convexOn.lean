-- Prove2me | solution 1 for ShorNonsmooth.Decomposition.valueFn_convexOn
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T13:42:59.79898+00:00
-- url     : https://prove2.me/submissions/beb940f3-5a70-4eea-9b8a-959593926e44

import Mathlib
import Definitions.Def_ShorNonsmooth_Decomposition_ValueFunction

set_option autoImplicit false

open ShorNonsmooth.Decomposition in
theorem ShorNonsmooth_valueFn_eq_of_optimal_80effeb9 {l m n : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (x : EuclideanSpace ℝ (Fin l)) (y : EuclideanSpace ℝ (Fin m))
    (hy : IsOptimalY f₀ f x y) : valueFn f₀ f x = f₀ x y := by
  unfold valueFn
  apply IsLeast.csInf_eq
  refine ⟨⟨y, hy.1, rfl⟩, ?_⟩
  rintro _ ⟨y', hy', rfl⟩
  exact hy.2 y' hy'

open ShorNonsmooth.Decomposition in
theorem ShorNonsmooth_jc_apply_80effeb9 {l m : ℕ}
    (F : EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (hF : JointlyConvex F) (x₁ x₂ : EuclideanSpace ℝ (Fin l)) (y₁ y₂ : EuclideanSpace ℝ (Fin m))
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    F (a • x₁ + b • x₂) (a • y₁ + b • y₂) ≤ a * F x₁ y₁ + b * F x₂ y₂ := by
  have := hF.2 (Set.mem_univ (x₁, y₁)) (Set.mem_univ (x₂, y₂)) ha hb hab
  simpa using this

open ShorNonsmooth.Decomposition in
theorem solution {l m n : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (hf₀ : JointlyConvex f₀) (hf : ∀ i, JointlyConvex (f i))
    (W : Set (EuclideanSpace ℝ (Fin l))) (hW : Convex ℝ W)
    (hWmin : ∀ x ∈ W, MinAttained f₀ f x) :
    ConvexOn ℝ W (valueFn f₀ f) := by
  refine ⟨hW, ?_⟩
  intro x₁ hx₁ x₂ hx₂ a b ha hb hab
  obtain ⟨y₁, hy₁⟩ := hWmin x₁ hx₁
  obtain ⟨y₂, hy₂⟩ := hWmin x₂ hx₂
  have hz : a • x₁ + b • x₂ ∈ W := hW hx₁ hx₂ ha hb hab
  obtain ⟨yz, hyz⟩ := hWmin _ hz
  rw [ShorNonsmooth_valueFn_eq_of_optimal_80effeb9 f₀ f x₁ y₁ hy₁,
    ShorNonsmooth_valueFn_eq_of_optimal_80effeb9 f₀ f x₂ y₂ hy₂,
    ShorNonsmooth_valueFn_eq_of_optimal_80effeb9 f₀ f _ yz hyz]
  have hfeas : a • y₁ + b • y₂ ∈ feasibleY f (a • x₁ + b • x₂) := by
    intro i
    have h1 : f i x₁ y₁ ≤ 0 := hy₁.1 i
    have h2 : f i x₂ y₂ ≤ 0 := hy₂.1 i
    have := ShorNonsmooth_jc_apply_80effeb9 (f i) (hf i) x₁ x₂ y₁ y₂ ha hb hab
    nlinarith [mul_nonpos_of_nonneg_of_nonpos ha h1, mul_nonpos_of_nonneg_of_nonpos hb h2]
  have h3 := hyz.2 _ hfeas
  have h4 := ShorNonsmooth_jc_apply_80effeb9 f₀ hf₀ x₁ x₂ y₁ y₂ ha hb hab
  simp only [smul_eq_mul]
  linarith
