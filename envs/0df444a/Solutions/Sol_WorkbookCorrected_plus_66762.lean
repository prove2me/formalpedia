-- Prove2me | solution 1 for WorkbookCorrected.plus_66762
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T15:45:18.765426+00:00
-- url     : https://prove2.me/submissions/d59414bf-f0d2-498c-b0c9-682c208c6956

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem solution (a : ℕ → ℝ) (h1 : a 1 = 1) (h2 : a 2 = 1) (h : ∀ n : ℕ, 1 ≤ n → a (n+2)=(a (n+1)+2/a n)/2) : ∀ n : ℕ, 1 ≤ n → 1 ≤ a n ∧ a n ≤ 2 := by
  have hp : ∀ n : ℕ, 1 ≤ a (n+1) ∧ a (n+1) ≤ 2 ∧ 1 ≤ a (n+2) ∧ a (n+2) ≤ 2 := by
    intro n
    induction n with
    | zero => norm_num [h1,h2]
    | succ n ih =>
      rcases ih with ⟨ha,hb,hc,hd⟩
      have hpos : 0 < a (n+1) := by linarith
      have hl : 1 ≤ 2/a (n+1) := (le_div_iff₀ hpos).2 (by simpa using hb)
      have hu : 2/a (n+1) ≤ 2 := (div_le_iff₀ hpos).2 (by linarith)
      have he := h (n+1) (by omega)
      refine ⟨hc,hd,?_,?_⟩ <;> simp only [Nat.add_assoc] at * <;> linarith
  intro n hn
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n≠0 by omega)
  exact ⟨(hp k).1,(hp k).2.1⟩
example : (∀ (a : ℕ → ℝ) (h1 : a 1 = 1) (h2 : a 2 = 1) (h : ∀ n : ℕ, 1 ≤ n → a (n+2)=(a (n+1)+2/a n)/2), ∀ n : ℕ, 1 ≤ n → 1 ≤ a n ∧ a n ≤ 2) := @solution
#print axioms solution
