-- Prove2me | solution 1 for WorkbookCorrected.plus_60440
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T15:30:29.670317+00:00
-- url     : https://prove2.me/submissions/ed573333-5350-43b1-bcef-c34c3caf58e8

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem solution (a : ℝ) (x : ℕ → ℝ) (ha : 2 < a) (ha3 : a ≤ 3)
    (h1 : x 1=a) (h : ∀ n : ℕ, 1 ≤ n → x (n+1)=x n^2/(2*(x n-1))) :
    ∀ n : ℕ, 1 ≤ n → x n ≤ 3 := by
  have hb : ∀ n : ℕ, 2 < x (n+1) ∧ x (n+1) ≤ 3 := by
    intro n
    induction n with
    | zero => rw [h1]; exact ⟨ha,ha3⟩
    | succ n ih =>
      have hd : 0 < 2*(x (n+1)-1) := by linarith [ih.1]
      rw [show n+1+1=(n+1)+1 by omega,h (n+1) (by omega)]
      constructor
      · apply (lt_div_iff₀ hd).mpr
        nlinarith only [sq_pos_of_pos (show 0 < x (n+1)-2 by linarith [ih.1])]
      · apply (div_le_iff₀ hd).mpr
        have hp := mul_nonneg (show 0 ≤ x (n+1)-2 by linarith [ih.1])
          (show 0 ≤ 3-x (n+1) by linarith [ih.2])
        nlinarith only [hp,ih.1]
  intro n hn
  obtain ⟨m,rfl⟩ : ∃ m : ℕ, n=m+1 := ⟨n-1,by omega⟩
  exact (hb m).2
example : (∀ (a : ℝ) (x : ℕ → ℝ) (ha : 2 < a) (ha3 : a ≤ 3)
    (h1 : x 1=a) (h : ∀ n : ℕ, 1 ≤ n → x (n+1)=x n^2/(2*(x n-1))),
    ∀ n : ℕ, 1 ≤ n → x n ≤ 3) := @solution
#print axioms solution
