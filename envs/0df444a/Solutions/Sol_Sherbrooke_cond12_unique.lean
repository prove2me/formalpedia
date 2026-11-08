-- Prove2me | solution 1 for Sherbrooke.cond12_unique
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:15:38.385234+00:00
-- url     : https://prove2.me/submissions/1cfcb892-0d43-4287-a38c-76de833acab3

import Mathlib
import Definitions.Def_Sherbrooke_lowerHull
import Definitions.Def_Sherbrooke_Cond12

open Sherbrooke in
theorem solution (c : ℝ) (Ξ : ℕ → ℝ) (hbdd : BddBelow (Set.range Ξ)) (m n : ℕ)
    (hm : Sherbrooke.Cond12 c Ξ m) (hn : Sherbrooke.Cond12 c Ξ n) : m = n := by
  have hne : ∀ m : ℕ, {y : ℝ | ∃ a b : ℝ, (∀ k : ℕ, a * (k : ℝ) + b ≤ Ξ k) ∧
      y = a * (m : ℝ) + b}.Nonempty := by
    intro m
    obtain ⟨B, hB⟩ := hbdd
    exact ⟨0 * (m : ℝ) + B, 0, B, fun k => by
      have := hB ⟨k, rfl⟩
      simpa using this, rfl⟩
  have hbd : ∀ m : ℕ, BddAbove {y : ℝ | ∃ a b : ℝ, (∀ k : ℕ, a * (k : ℝ) + b ≤ Ξ k) ∧
      y = a * (m : ℝ) + b} := by
    intro m
    refine ⟨Ξ m, ?_⟩
    rintro y ⟨a, b, h, rfl⟩
    exact h m
  have hle : ∀ (m : ℕ) (a b : ℝ), (∀ k : ℕ, a * (k : ℝ) + b ≤ Ξ k) →
      a * (m : ℝ) + b ≤ Sherbrooke.lowerHull Ξ m :=
    fun m a b h => le_csSup (hbd m) ⟨a, b, h, rfl⟩
  have hconv : ∀ m : ℕ, 2 * Sherbrooke.lowerHull Ξ (m + 1) ≤
      Sherbrooke.lowerHull Ξ m + Sherbrooke.lowerHull Ξ (m + 1 + 1) := by
    intro m
    have : Sherbrooke.lowerHull Ξ (m + 1) ≤
        (Sherbrooke.lowerHull Ξ m + Sherbrooke.lowerHull Ξ (m + 1 + 1)) / 2 := by
      refine csSup_le (hne (m + 1)) ?_
      rintro y ⟨a, b, h, rfl⟩
      have h1 := hle m a b h
      have h2 := hle (m + 1 + 1) a b h
      push_cast at h1 h2 ⊢
      linarith
    linarith
  have hmono : ∀ i j : ℕ, i ≤ j →
      Sherbrooke.lowerHull Ξ (i + 1) - Sherbrooke.lowerHull Ξ i ≤
        Sherbrooke.lowerHull Ξ (j + 1) - Sherbrooke.lowerHull Ξ j := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ j hj ih =>
      have := hconv j
      linarith
  have key : ∀ m n : ℕ, Sherbrooke.Cond12 c Ξ m → Sherbrooke.Cond12 c Ξ n → ¬ m < n := by
    intro m n hm hn hlt
    have hn2 : c + Sherbrooke.lowerHull Ξ n - Sherbrooke.lowerHull Ξ (n - 1) < 0 := by
      rcases hn.2 with h | h
      · omega
      · exact h
    have h3 := hmono m (n - 1) (by omega)
    have e : n - 1 + 1 = n := by omega
    rw [e] at h3
    linarith [hm.1]
  rcases lt_trichotomy m n with h | h | h
  · exact absurd h (key m n hm hn)
  · exact h
  · exact absurd h (key n m hn hm)
