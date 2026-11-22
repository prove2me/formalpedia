-- Prove2me | solution 1 for SubmodOrder.thresholdAdd_value_ge
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T23:09:18.744134+00:00
-- url     : https://prove2.me/submissions/4c10cd88-37a9-4f20-8846-8fe9a1c19fea

import Mathlib
import Definitions.Def_SubmodOrder_thresholdAdd

set_option autoImplicit false

open SubmodOrder

theorem SubmodOrder.taLoop_invariant_aux {α : Type*} [DecidableEq α] (f : Finset α → ℝ) (k : ℕ)
    (τ : ℝ) : ∀ (l : List α) (S : Finset α) (v : ℝ), S.card ≤ k → v = f S →
      (S.card : ℝ) * τ ≤ v →
      (OracleProg.run f (taLoop k τ l S v)).1.card ≤ k ∧
      ((OracleProg.run f (taLoop k τ l S v)).1.card : ℝ) * τ ≤
        f (OracleProg.run f (taLoop k τ l S v)).1 := by
  intro l
  induction l with
  | nil =>
    intro S v hk hv hτ
    simp only [taLoop, OracleProg.run]
    exact ⟨hk, hv ▸ hτ⟩
  | cons e es ih =>
    intro S v hk hv hτ
    simp only [taLoop]
    split_ifs with hc
    · simp only [OracleProg.run]
      split_ifs with ht
      · apply ih
        · exact (Finset.card_insert_le e S).trans (by omega)
        · rfl
        · by_cases he : e ∈ S
          · rw [Finset.insert_eq_of_mem he]
            exact hv ▸ hτ
          · rw [Finset.card_insert_eq_ite, if_neg he]
            push_cast
            linarith
      · exact ih S v hk hv hτ
    · simp only [OracleProg.run]
      exact ⟨hk, hv ▸ hτ⟩

theorem solution {α : Type*} [DecidableEq α] {n : ℕ} (π : α ≃ Fin n) (k : ℕ)
    (τ : ℝ) (f : Finset α → ℝ) (hf0 : f ∅ = 0) :
    (OracleProg.run f (thresholdAdd π k τ)).1.card ≤ k ∧
      ((OracleProg.run f (thresholdAdd π k τ)).1.card : ℝ) * τ ≤
        f (OracleProg.run f (thresholdAdd π k τ)).1 := by
  unfold thresholdAdd
  exact SubmodOrder.taLoop_invariant_aux f k τ (orderList π) ∅ 0 (by simp) hf0.symm (by simp)
