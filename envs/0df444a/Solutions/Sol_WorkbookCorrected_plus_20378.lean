-- Prove2me | solution 1 for WorkbookCorrected.plus_20378
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T14:27:26.644649+00:00
-- url     : https://prove2.me/submissions/1a26a971-fe6f-45d5-a1bd-2de1e31b0fff

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a : ℕ → ℝ) (h0 : a 1=1)
    (h : ∀ n : ℕ, 1≤n → a (n+1)=a n+1/a n) :
    ∀ M : ℝ, ∃ N : ℕ, ∀ n : ℕ, N≤n → M<a n := by
  have hg : ∀ n : ℕ, 0<a (n+1) ∧ 2*(n:ℝ)+1 ≤ (a (n+1))^2 := by
    intro n
    induction n with
    | zero => norm_num [h0]
    | succ n ih =>
      rw [h (n+1) (by omega)]
      constructor
      · have hp := ih.1
        positivity
      · have hi : (a (n+1)+1/a (n+1))^2=(a (n+1))^2+2+(1/a (n+1))^2 := by
          have hp := ih.1
          field_simp
          <;> ring
        push_cast
        nlinarith only [hi,ih.2,sq_nonneg (1/a (n+1))]
  intro M
  obtain ⟨K,hK⟩ := exists_nat_gt (M^2+1)
  refine ⟨K+1,?_⟩
  intro n hn
  have hn1 : 1≤n := by omega
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n≠0 by omega)
  have hm : K ≤ m := by omega
  have hmc : (K:ℝ) ≤ m := by exact_mod_cast hm
  have hs : M^2<(a (m+1))^2 := by nlinarith only [hK,hmc,(hg m).2,sq_nonneg M]
  exact lt_of_le_of_lt (le_abs_self M) (abs_lt_of_sq_lt_sq hs (le_of_lt (hg m).1))
example : (∀ (a : ℕ → ℝ) (h0 : a 1=1)
    (h : ∀ n : ℕ, 1≤n → a (n+1)=a n+1/a n),
    ∀ M : ℝ, ∃ N : ℕ, ∀ n : ℕ, N≤n → M<a n) := @solution
#print axioms solution
