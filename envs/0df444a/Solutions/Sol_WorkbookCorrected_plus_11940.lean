-- Prove2me | solution 1 for WorkbookCorrected.plus_11940
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T14:17:46.53869+00:00
-- url     : https://prove2.me/submissions/998389d8-db52-40a5-bf8c-f352208f6a6c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x : ℕ → ℝ)
    (h : ∀ n : ℕ, 1≤n → (x (n+1)-x n)*(x (n+1)+x n+1) ≤ 0) :
    ∃ M : ℝ, ∀ n : ℕ, 1≤n → |x n| ≤ M := by
  have hs : ∀ n : ℕ, 1≤n → (2*x n+1)^2 ≤ (2*x 1+1)^2 := by
    intro n hn
    induction n,hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih => nlinarith only [ih,h n hn]
  refine ⟨(|2*x 1+1|+1)/2,?_⟩
  intro n hn
  have hh : (2*x n+1)^2 ≤ |2*x 1+1|^2 := by simpa only [sq_abs] using hs n hn
  have hb := abs_le_of_sq_le_sq' hh (abs_nonneg (2*x 1+1))
  apply abs_le.mpr
  constructor <;> linarith only [hb.1,hb.2]
example : (∀ (x : ℕ → ℝ)
    (h : ∀ n : ℕ, 1≤n → (x (n+1)-x n)*(x (n+1)+x n+1) ≤ 0),
    ∃ M : ℝ, ∀ n : ℕ, 1≤n → |x n| ≤ M) := @solution
#print axioms solution
