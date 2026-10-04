-- Prove2me | solution 1 for StarShapedRisk.LawInvariant.inf_envelope_star_shaped
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T03:07:55.983022+00:00
-- url     : https://prove2.me/submissions/b9c11d36-2038-4c0b-b252-7c88368f8870

import Mathlib

set_option autoImplicit false

theorem solution {E : Type*} [AddCommGroup E] [Module ℝ E]
    (φ : (Set.Ioo (0 : ℝ) 1 → ℝ) → E → EReal)
    (G : Set (Set.Ioo (0 : ℝ) 1 → ℝ))
    (hφ : ∀ g ∈ G, ∀ {t : ℝ}, 1 < t → ∀ X : E,
      φ g (t • X) = ((t : EReal) * φ ((t⁻¹ : ℝ) • g) X))
    (hG : ∀ {t : ℝ}, 1 < t → ∀ g ∈ G, (t⁻¹ : ℝ) • g ∈ G)
    {t : ℝ} (ht : 1 < t) (X : E) :
    (t : EReal) * (⨅ g ∈ G, φ g X) ≤ ⨅ g ∈ G, φ g (t • X) := by
  refine le_iInf₂ fun g hg => ?_
  rw [hφ g hg ht X]
  have h0 : (0 : EReal) ≤ (t : EReal) := by
    exact_mod_cast (le_of_lt (lt_trans zero_lt_one ht))
  exact mul_le_mul_of_nonneg_left (iInf₂_le _ (hG ht g hg)) h0
