-- Prove2me | solution 1 for ProcessingNetworks.CTMCFoster.lemma_D_9
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T22:17:18.378208+00:00
-- url     : https://prove2.me/submissions/1de630c3-4146-4262-afa0-67c38c9c1103

import Mathlib
import Definitions.Def_MatrixAnalytic_ProductForm_Chain
import Definitions.Def_ProcessingNetworks_CTMCFoster_IsInvariantMeasure

open ProcessingNetworks.CTMCFoster MatrixAnalytic.ProductForm in
theorem solution {S : Type*} [Countable S] [DecidableEq S] {Λ : S → S → ℝ}
    (hΛ : IsGeneratorC Λ) (η μ : S → ℝ) (hη : ∀ i, 0 ≤ η i)
    (hμ : ∀ i, μ i = holdRate Λ i * η i) :
    IsInvariantMeasure Λ η ↔ ∀ y, HasSum (fun x => μ x * jumpP Λ x y) (μ y) := by
  have hq : ∀ x, holdRate Λ x ≠ 0 := fun x => by
    unfold holdRate
    exact (neg_pos.mpr (hΛ.2.1 x)).ne'
  have hg : ∀ y, (fun x => μ x * jumpP Λ x y)
      = fun x => η x * Λ x y - (if x = y then η y * Λ y y else 0) := by
    intro y
    funext x
    rw [hμ x]
    unfold jumpP
    by_cases hxy : x = y
    · subst hxy
      simp
    · rw [if_neg (Ne.symm hxy), if_neg hxy, sub_zero]
      have := hq x
      field_simp
  constructor
  · intro h y
    rw [hg y]
    have h2 := (h y).sub (hasSum_ite_eq y (η y * Λ y y))
    have hv : (0 : ℝ) - η y * Λ y y = μ y := by
      rw [hμ y]; unfold holdRate; ring
    rw [hv] at h2
    exact h2
  · intro h y
    have h1 := h y
    rw [hg y] at h1
    have h2 := h1.add (hasSum_ite_eq y (η y * Λ y y))
    simp only [sub_add_cancel] at h2
    have hv : μ y + η y * Λ y y = 0 := by
      rw [hμ y]; unfold holdRate; ring
    rw [hv] at h2
    exact h2
