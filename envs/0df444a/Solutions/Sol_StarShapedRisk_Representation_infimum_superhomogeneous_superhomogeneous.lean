-- Prove2me | solution 1 for StarShapedRisk.Representation.infimum_superhomogeneous_superhomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @He Jiankui
-- created : 2026-10-01T20:38:34.945297+00:00
-- url     : https://prove2.me/submissions/3b2b208b-b809-461a-b9e9-6b94a9efd404

import Mathlib

theorem solution {E : Type*} [AddCommGroup E] [Module ℝ E]
    (Γ : Set (E → ℝ)) (ρ : E → ℝ)
    (hsup : ∀ γ ∈ Γ, ∀ {t : ℝ}, 1 < t → ∀ X, t * γ X ≤ γ (t • X))
    (hmin : ∀ X : E, IsLeast ((fun γ => γ X) '' Γ) (ρ X))
    {t : ℝ} (ht : 1 < t) (X : E) :
    t * ρ X ≤ ρ (t • X) := by
  obtain ⟨γ, hγ, hγeq⟩ := (hmin (t • X)).1
  have hle : ρ X ≤ γ X := (hmin X).2 (Set.mem_image_of_mem _ hγ)
  have ht0 : 0 ≤ t := le_of_lt (lt_trans zero_lt_one ht)
  have h1 : t * ρ X ≤ t * γ X := mul_le_mul_of_nonneg_left hle ht0
  have h2 : t * γ X ≤ γ (t • X) := hsup γ hγ ht X
  calc
    t * ρ X ≤ t * γ X := h1
    _ ≤ γ (t • X) := h2
    _ = ρ (t • X) := hγeq
