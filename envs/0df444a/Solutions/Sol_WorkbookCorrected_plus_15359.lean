-- Prove2me | solution 1 for WorkbookCorrected.plus_15359
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T14:22:17.494214+00:00
-- url     : https://prove2.me/submissions/37328f34-50c5-4e50-835e-a60217badb1a

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
open scoped BigOperators
theorem solution (a : ℕ → ℝ) (h0 : a 1=1/2)
    (h : ∀ n : ℕ, 1≤n → a (n+1)=(2*(n:ℝ)-1)/(2*((n:ℝ)+1))*a n) :
    ∀ n : ℕ, 1≤n → ∑ k ∈ Finset.range n, a (k+1) < 1 := by
  have hp : ∀ n : ℕ, 0<a (n+1) := by
    intro n
    induction n with
    | zero => norm_num [h0]
    | succ n ih =>
      rw [h (n+1) (by omega)]
      have hn : (0:ℝ)≤n := Nat.cast_nonneg n
      push_cast
      apply mul_pos _ ih
      apply div_pos <;> linarith only [hn]
  have hi : ∀ n : ℕ, ∑ k ∈ Finset.range n, a (k+1)=1-2*((n:ℝ)+1)*a (n+1) := by
    intro n
    induction n with
    | zero => norm_num [h0]
    | succ n ih =>
      rw [Finset.sum_range_succ,ih,h (n+1) (by omega)]
      push_cast
      have hn : (0:ℝ)≤n := Nat.cast_nonneg n
      have hd : (2:ℝ)*((n:ℝ)+1+1) ≠ 0 := by positivity
      field_simp
      <;> ring
  intro n hn
  rw [hi n]
  have hh : 0<2*((n:ℝ)+1)*a (n+1) := mul_pos (by positivity) (hp n)
  linarith only [hh]
example : (∀ (a : ℕ → ℝ) (h0 : a 1=1/2)
    (h : ∀ n : ℕ, 1≤n → a (n+1)=(2*(n:ℝ)-1)/(2*((n:ℝ)+1))*a n),
    ∀ n : ℕ, 1≤n → ∑ k ∈ Finset.range n, a (k+1) < 1) := @solution
#print axioms solution
