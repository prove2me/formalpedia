-- Prove2me | solution 1 for WorkbookSource.plus_57482
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T15:28:34.347338+00:00
-- url     : https://prove2.me/submissions/e1fd64b2-8a88-4917-9d55-164b6909987d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem solution (x : ℕ → ℝ)
    (h : ∀ n : ℕ, 2*x n=x (n-1)+Real.sqrt (3-3*(x (n-1))^2)) :
    ∃ M : ℝ, ∀ n : ℕ, |x n| < M := by
  let B := max |x 0| (Real.sqrt 3)
  have hroot : Real.sqrt 3 ≤ B := le_max_right _ _
  have hb : ∀ n : ℕ, |x n| ≤ B := by
    intro n
    induction n with
    | zero => exact le_max_left _ _
    | succ n ih =>
      have hh := h (n+1)
      rw [Nat.add_sub_cancel] at hh
      have hr : Real.sqrt (3-3*(x n)^2) ≤ Real.sqrt 3 :=
        Real.sqrt_le_sqrt (by nlinarith only [sq_nonneg (x n)])
      have ha := abs_add_le (x n) (Real.sqrt (3-3*(x n)^2))
      rw [abs_of_nonneg (Real.sqrt_nonneg _)] at ha
      have he := congrArg abs hh
      rw [abs_mul] at he
      norm_num at he
      linarith only [ih,hr,ha,he,hroot]
  refine ⟨B+1,?_⟩
  intro n
  linarith [hb n]
example : (∀ (x : ℕ → ℝ)
    (h : ∀ n : ℕ, 2*x n=x (n-1)+Real.sqrt (3-3*(x (n-1))^2)),
    ∃ M : ℝ, ∀ n : ℕ, |x n| < M) := @solution
#print axioms solution
