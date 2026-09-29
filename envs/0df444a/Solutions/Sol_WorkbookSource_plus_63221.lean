-- Prove2me | solution 1 for WorkbookSource.plus_63221
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T15:39:55.711273+00:00
-- url     : https://prove2.me/submissions/2f4c7600-4f86-463e-bf8a-b6f67f640bec

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem solution (a : ℕ → ℝ) (a0 : a 0 = 0) (a1 : a 1 = 0) (a2 : a 2 = -1) (a3 : a 3 = 0)
    (h : ∀ n, a (n + 4) + 2 * a (n + 3) + 3 * a (n + 2) + 2 * a (n + 1) + a n = 0) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n > N, |a n / n ^ 2| < ε := by
  have hf : ∀ k : ℕ, a (3*k)= 0 ∧ a (3*k+1)=3*(k:ℝ) ∧ a (3*k+2)= -3*(k:ℝ)-1 ∧ a (3*k+3)=0 := by
    intro k
    induction k with
    | zero => simpa using And.intro a0 (And.intro a1 (And.intro a2 a3))
    | succ k ih =>
      have h0 := h (3*k)
      have h1 := h (3*k+1)
      have h2 := h (3*k+2)
      have h3 := h (3*k+3)
      rcases ih with ⟨ih0,ih1,ih2,ih3⟩
      norm_num [Nat.mul_add, Nat.add_assoc] at *
      constructor
      · linarith
      constructor
      · linarith
      constructor <;> linarith
  intro ε he
  obtain ⟨N,hN⟩ := exists_nat_gt (1/ε)
  refine ⟨N,?_⟩
  intro n hn
  have hn0 : 0 < n := by omega
  have hnR : (0:ℝ) < n := by exact_mod_cast hn0
  have hb : |a n| ≤ (n:ℝ) := by
    have hh := hf (n/3)
    have hr : n%3=0 ∨ n%3=1 ∨ n%3=2 := by omega
    have hd := Nat.mod_add_div n 3
    rcases hh with ⟨h0,h1,h2,h3⟩
    rcases hr with hr|hr|hr
    · have hn' : n=3*(n/3) := by omega
      rw [hn',h0,abs_zero]
      push_cast
      nlinarith [Nat.cast_nonneg (n/3) (α:=ℝ)]
    · have hn' : n=3*(n/3)+1 := by omega
      rw [hn',h1,abs_of_nonneg (by positivity)]
      push_cast
      nlinarith [Nat.cast_nonneg (n/3) (α:=ℝ)]
    · have hn' : n=3*(n/3)+2 := by omega
      rw [hn',h2,abs_of_nonpos (by have hh : (0:ℝ) ≤ (n/3:ℕ) := Nat.cast_nonneg _; linarith : -3*((n/3:ℕ):ℝ)-1 ≤ (0:ℝ))]
      push_cast
      nlinarith [Nat.cast_nonneg (n/3) (α:=ℝ)]
  have hnr : 1/ε < (n:ℝ) := lt_trans hN (by exact_mod_cast hn)
  have heN : 1/(n:ℝ) < ε := (div_lt_iff₀ hnR).2 (by have hh := (div_lt_iff₀ he).1 hnr; nlinarith)
  calc
    |a n / (n:ℝ)^2| = |a n| / (n:ℝ)^2 := by rw [abs_div,abs_of_nonneg (sq_nonneg (n:ℝ))]
    _ ≤ (n:ℝ)/(n:ℝ)^2 := (div_le_div_iff_of_pos_right (sq_pos_of_pos hnR)).2 hb
    _ = 1/(n:ℝ) := by field_simp <;> ring
    _ < ε := heN
example : (∀ (a : ℕ → ℝ) (a0 : a 0 = 0) (a1 : a 1 = 0) (a2 : a 2 = -1) (a3 : a 3 = 0) (h : ∀ n, a (n + 4) + 2 * a (n + 3) + 3 * a (n + 2) + 2 * a (n + 1) + a n = 0), ∀ ε > 0, ∃ N : ℕ, ∀ n > N, |a n / n ^ 2| < ε  ) := @solution
#print axioms solution
