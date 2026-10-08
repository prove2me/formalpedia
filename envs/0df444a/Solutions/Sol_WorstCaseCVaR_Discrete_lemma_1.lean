-- Prove2me | solution 1 for WorstCaseCVaR.Discrete.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T03:30:03.069982+00:00
-- url     : https://prove2.me/submissions/c3ad0b01-da05-4262-b77a-c3ab330351b5

import Definitions.Def_WorstCaseCVaR_Discrete_Setting

section
set_option autoImplicit false
namespace CVaRCodex

/-- Lemma 1, Zhu & Fukushima (2009), p. 1157 (Fan 1953): for nonempty compact convex
`𝒳 ⊆ ℝⁿ`, `𝒴 ⊆ ℝᵐ` and `φ(x, y)` convex and lower semicontinuous in `x` for each `y ∈ 𝒴`, concave
and upper semicontinuous in `y` for each `x ∈ 𝒳`, `φ` has a saddle point `(x₀, y₀)` on `𝒳 × 𝒴`;
equivalently, `min_{x ∈ 𝒳} max_{y ∈ 𝒴} φ(x, y) = max_{y ∈ 𝒴} min_{x ∈ 𝒳} φ(x, y)` with every
minimum and maximum attained. The semicontinuity hypotheses are not printed in the paper; they
are needed for the minima and maxima to exist. -/
theorem lemma_1 {n m : ℕ} (X : Set (Fin n → ℝ)) (Y : Set (Fin m → ℝ))
    (hXne : X.Nonempty) (hXc : IsCompact X) (hXcv : Convex ℝ X)
    (hYne : Y.Nonempty) (hYc : IsCompact Y) (hYcv : Convex ℝ Y)
    (φ : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (hconv : ∀ y ∈ Y, ConvexOn ℝ X (fun x => φ x y))
    (hconc : ∀ x ∈ X, ConcaveOn ℝ Y (fun y => φ x y))
    (hlsc : ∀ y ∈ Y, LowerSemicontinuousOn (fun x => φ x y) X)
    (husc : ∀ x ∈ X, UpperSemicontinuousOn (fun y => φ x y) Y) :
    ∃ x₀ ∈ X, ∃ y₀ ∈ Y, ∀ x ∈ X, ∀ y ∈ Y, φ x₀ y ≤ φ x₀ y₀ ∧ φ x₀ y₀ ≤ φ x y₀ := by
  obtain ⟨a,ha,b,hb,hs⟩ := Sion.exists_isSaddlePointOn hXne hXcv hXc hlsc
    (fun y hy ↦ (hconv y hy).quasiconvexOn) hYcv hYne hYc husc
    (fun x hx ↦ (hconc x hx).quasiconcaveOn)
  exact ⟨a,ha,b,hb,fun x hx y hy ↦ ⟨hs a ha y hy,hs x hx b hb⟩⟩


end CVaRCodex

end


section
set_option autoImplicit false
theorem solution {n m : ℕ} (X : Set (Fin n → ℝ)) (Y : Set (Fin m → ℝ))
    (hXne : X.Nonempty) (hXc : IsCompact X) (hXcv : Convex ℝ X)
    (hYne : Y.Nonempty) (hYc : IsCompact Y) (hYcv : Convex ℝ Y)
    (φ : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (hconv : ∀ y ∈ Y, ConvexOn ℝ X (fun x => φ x y))
    (hconc : ∀ x ∈ X, ConcaveOn ℝ Y (fun y => φ x y))
    (hlsc : ∀ y ∈ Y, LowerSemicontinuousOn (fun x => φ x y) X)
    (husc : ∀ x ∈ X, UpperSemicontinuousOn (fun y => φ x y) Y) :
    ∃ x₀ ∈ X, ∃ y₀ ∈ Y, ∀ x ∈ X, ∀ y ∈ Y, φ x₀ y ≤ φ x₀ y₀ ∧ φ x₀ y₀ ≤ φ x y₀ := by
  exact CVaRCodex.lemma_1 X Y hXne hXc hXcv hYne hYc hYcv φ hconv hconc hlsc husc

end

#print axioms solution
