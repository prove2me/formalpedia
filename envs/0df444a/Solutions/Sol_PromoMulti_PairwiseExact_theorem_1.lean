-- Prove2me | solution 1 for PromoMulti.PairwiseExact.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T07:29:11.455921+00:00
-- url     : https://prove2.me/submissions/7cd1c52c-d239-40a9-b67e-9510c0cdb519

import Mathlib
import Definitions.Def_PromoMulti_PairwiseExact_Model
import Theorems.Thm_PromoMulti_PairwiseExact_higher_order_coef_zero

open PromoMulti.PairwiseExact

theorem solution {N T : ℕ} (I : Instance N T)
    (h : (i : Fin N) → Fin T → (Fin (I.M i + 1) → ℝ) → ℝ) (H : Fin N → Fin N → Fin T → ℝ → ℝ)
    (hsep : AdditiveCross I h H) (R : Rules N T) (κ : ℕ) (hκ : 2 ≤ κ) (hκN : κ ≤ N) :
    (∀ γ : Plan I, appObj I κ γ = appObj I 2 γ) ∧
    (∀ γ : Plan I, IsOptimalApp I R κ γ ↔ IsOptimalApp I R 2 γ) := by
  have h1 : ∀ γ : Plan I, appObj I κ γ = appObj I 2 γ := by
    intro γ
    unfold appObj
    congr 1
    refine Finset.sum_congr rfl (fun t _ => ?_)
    symm
    apply Finset.sum_subset
    · intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
      omega
    · intro σ hσ hσ2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_le] at hσ hσ2
      have h3 : 3 ≤ (supp σ).card := by have := hσ2 hσ.1; omega
      rw [higher_order_coef_zero I h H hsep t σ h3, zero_mul]
  refine ⟨h1, fun γ => ?_⟩
  simp only [IsOptimalApp, h1]
