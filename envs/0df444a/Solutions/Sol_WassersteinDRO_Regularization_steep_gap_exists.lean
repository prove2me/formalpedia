-- Prove2me | solution 1 for WassersteinDRO.Regularization.steep_gap_exists
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-10-05T20:49:40.582824+00:00
-- url     : https://prove2.me/submissions/d8dd1d0f-c556-40bd-8fb5-3a3dca8a0dfd

import Mathlib
import Definitions.Def_WassersteinDRO_Regularization_lipschitzModulus

set_option autoImplicit false

open WassersteinDRO.Regularization

theorem solution {E : Type*} [NormedAddCommGroup E] (ℓ : E → ℝ)
    (lam : ℝ) (hlam : 0 ≤ lam) (hlt : ENNReal.ofReal lam < lipschitzModulus ℓ) :
    ∃ x y : E, x ≠ y ∧ lam * ‖x - y‖ < ℓ x - ℓ y := by
  by_contra hcon
  -- Contrapositive hypothesis: every secant gap is bounded by `lam`.
  have hbound : ∀ x y : E, x ≠ y → ℓ x - ℓ y ≤ lam * ‖x - y‖ := by
    intro x y hxy
    by_contra hlt'
    exact hcon ⟨x, y, hxy, not_le.mp hlt'⟩
  -- Swapping x/y gives the two-sided bound on the absolute difference.
  have habs : ∀ x y : E, x ≠ y → |ℓ x - ℓ y| ≤ lam * ‖x - y‖ := by
    intro x y hxy
    rw [abs_le]
    refine ⟨?_, hbound x y hxy⟩
    have hswap := hbound y x (Ne.symm hxy)
    rw [norm_sub_rev] at hswap
    linarith
  -- Hence every term of the sup defining `lipschitzModulus` is ≤ `ofReal lam`.
  have hterm : ∀ x y : E, (hxy : x ≠ y) →
      ENNReal.ofReal (|ℓ x - ℓ y| / ‖x - y‖) ≤ ENNReal.ofReal lam := by
    intro x y hxy
    have hnorm : 0 < ‖x - y‖ := by
      rw [norm_pos_iff, sub_ne_zero]
      exact hxy
    have hdiv : |ℓ x - ℓ y| / ‖x - y‖ ≤ lam := by
      rw [div_le_iff₀ hnorm]
      exact habs x y hxy
    exact (ENNReal.ofReal_le_ofReal_iff hlam).mpr hdiv
  -- Push the bound through the triple-binder sup.
  have hsup : lipschitzModulus ℓ ≤ ENNReal.ofReal lam := by
    unfold lipschitzModulus
    apply iSup_le; intro x
    apply iSup_le; intro y
    apply iSup_le; intro hxy
    exact hterm x y hxy
  exact (not_le_of_gt hlt) hsup

theorem WassersteinDRO.Regularization.steep_gap_exists {E : Type*} [NormedAddCommGroup E]
    (ℓ : E → ℝ)
    (lam : ℝ) (hlam : 0 ≤ lam) (hlt : ENNReal.ofReal lam < lipschitzModulus ℓ) :
    ∃ x y : E, x ≠ y ∧ lam * ‖x - y‖ < ℓ x - ℓ y :=
  solution ℓ lam hlam hlt
