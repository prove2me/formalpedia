-- Prove2me | solution 1 for WorkbookCorrected.plus_11171
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T14:14:22.222719+00:00
-- url     : https://prove2.me/submissions/3fa5fe39-70c7-420b-8e2b-603d1dbe06e6

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
open scoped BigOperators
theorem solution (x : ℕ → ℝ) (h0 : x 1=1/2)
    (h : ∀ k : ℕ, 1≤k → x (k+1)=(x k)^2+x k) :
    ⌊∑ k ∈ Finset.range 100, (1/(x (k+1)+1))⌋ = (1:ℤ) := by
  have hp : ∀ n : ℕ, 0<x (n+1) := by
    intro n
    induction n with
    | zero => norm_num [h0]
    | succ n ih => rw [h (n+1) (by omega)]; positivity
  have htel : ∀ n : ℕ, ∑ k ∈ Finset.range n, (1/(x (k+1)+1))=2-1/x (n+1) := by
    intro n
    induction n with
    | zero => norm_num [h0]
    | succ n ih =>
      rw [Finset.sum_range_succ,ih,h (n+1) (by omega)]
      have hn := hp n
      field_simp
      <;> ring
  have h2 : x 2=3/4 := by rw [h 1 (by omega),h0]; norm_num
  have h3 : x 3=21/16 := by rw [h 2 (by omega),h2]; norm_num
  have hlarge : ∀ n : ℕ, 3≤n → 1<x n := by
    intro n hn
    induction n,hn using Nat.le_induction with
    | base => norm_num [h3]
    | succ n hn ih => rw [h n (by omega)]; nlinarith only [ih,sq_nonneg (x n)]
  have hb := hlarge 101 (by omega)
  have hi : 0<1/x 101 := by positivity
  have hj : 1/x 101 < 1 := (div_lt_iff₀ (by linarith : 0<x 101)).mpr (by linarith)
  rw [htel 100]
  apply Int.floor_eq_iff.mpr
  norm_num only [Int.cast_one, Nat.reduceAdd]
  constructor <;> linarith only [hi,hj]
example : (∀ (x : ℕ → ℝ) (h0 : x 1=1/2)
    (h : ∀ k : ℕ, 1≤k → x (k+1)=(x k)^2+x k),
    ⌊∑ k ∈ Finset.range 100, (1/(x (k+1)+1))⌋ = (1:ℤ)) := @solution
#print axioms solution
