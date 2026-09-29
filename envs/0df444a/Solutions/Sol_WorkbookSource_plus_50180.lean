-- Prove2me | solution 1 for WorkbookSource.plus_50180
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T16:14:58.905276+00:00
-- url     : https://prove2.me/submissions/87197903-50eb-4962-a891-bdd6c166a2bb

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
private lemma bound (a : ℕ → ℝ) : ∀ n : ℕ,
    1 ≤ ∏ k ∈ Finset.range n, max 1 (a k) ∧
    (∑ k ∈ Finset.range n, a k) ≤ (n:ℝ)+(∏ k ∈ Finset.range n, max 1 (a k))-1 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ,Finset.sum_range_succ]
    push_cast
    have hm : 1 ≤ max 1 (a n) := le_max_left _ _
    have ha : a n ≤ max 1 (a n) := le_max_right _ _
    have hp := mul_nonneg (sub_nonneg.mpr ih.1) (sub_nonneg.mpr hm)
    constructor
    · nlinarith only [hp,ih.1,hm]
    · nlinarith only [hp,ih.2,ha]

theorem solution (a : ℕ → ℝ) (ha : ∀ k : ℕ, 0 < a k) :
    (∑ k ∈ Finset.range 95, a k) ≤ 94+∏ k ∈ Finset.range 95, max 1 (a k) := by
  have hh := (bound a 95).2
  norm_num at hh
  linarith only [hh]
example : (∀ (a : ℕ → ℝ) (ha : ∀ k : ℕ, 0 < a k),
    (∑ k ∈ Finset.range 95, a k) ≤ 94+∏ k ∈ Finset.range 95, max 1 (a k)) := @solution
#print axioms solution
