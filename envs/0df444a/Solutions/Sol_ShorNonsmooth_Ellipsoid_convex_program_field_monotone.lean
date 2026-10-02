-- Prove2me | solution 1 for ShorNonsmooth.Ellipsoid.convex_program_field_monotone
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T10:12:50.092319+00:00
-- url     : https://prove2.me/submissions/50602bc9-84bb-4983-b599-ad9b10643282

import Mathlib

theorem solution {n m : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin n) → ℝ) (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf₀ : ConvexOn ℝ Set.univ f₀) (hf : ∀ i, ConvexOn ℝ Set.univ (f i))
    (g₀ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (gc : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg₀ : ∀ x y : EuclideanSpace ℝ (Fin n), f₀ y - f₀ x ≥ inner ℝ (g₀ x) (y - x))
    (hgc : ∀ i, ∀ x y : EuclideanSpace ℝ (Fin n), f i y - f i x ≥ inner ℝ (gc i x) (y - x))
    (xstar : EuclideanSpace ℝ (Fin n)) (hfeas : ∀ i, f i xstar ≤ 0)
    (hopt : ∀ x : EuclideanSpace ℝ (Fin n), (∀ i, f i x ≤ 0) → f₀ xstar ≤ f₀ x)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg_feas : ∀ x, (∀ i, f i x ≤ 0) → g x = g₀ x)
    (hg_infeas : ∀ x, (∃ i, 0 < f i x) →
      ∃ istar : Fin m, (∀ j, f j x ≤ f istar x) ∧ g x = gc istar x) :
    ∀ x : EuclideanSpace ℝ (Fin n), 0 ≤ inner ℝ (g x) (x - xstar) := by
  intro x
  have key : ∀ v : EuclideanSpace ℝ (Fin n),
      inner ℝ v (xstar - x) = - inner ℝ v (x - xstar) := by
    intro v
    rw [← inner_neg_right, neg_sub]
  by_cases hx : ∀ i, f i x ≤ 0
  · rw [hg_feas x hx]
    have h1 := hg₀ x xstar
    have h2 := hopt x hx
    rw [key] at h1
    linarith
  · simp only [not_forall, not_le] at hx
    obtain ⟨istar, hmax, hgx⟩ := hg_infeas x hx
    obtain ⟨i, hi⟩ := hx
    rw [hgx]
    have h1 := hgc istar x xstar
    have h2 := hfeas istar
    have h3 := hmax i
    rw [key] at h1
    linarith
