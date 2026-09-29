-- Prove2me | solution 1 for WorkbookCorrected.plus_16969
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T14:23:02.158349+00:00
-- url     : https://prove2.me/submissions/7e4a298f-60ba-4ac8-8755-b94dddf838b8

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
private lemma invariant (x : ℝ) (hl : 4/5<x) (hu : x≤5/4) :
    4/5<(x^4+9)/(10*x) ∧ (x^4+9)/(10*x)≤5/4 := by
  have hp : 0<10*x := by linarith
  constructor
  · apply (lt_div_iff₀ hp).mpr
    have hh : 0≤(x-1)^2*(x^2+2*x+3) := by positivity
    nlinarith only [hh,hu]
  · apply (div_le_iff₀ hp).mpr
    have hsq : x^2≤25/16 := by nlinarith only [hl,hu,sq_nonneg (x-5/4)]
    have h4 := mul_nonneg (sub_nonneg.mpr hsq) (sq_nonneg x)
    have hh := mul_nonneg (show 0≤x-4/5 by linarith) (show 0≤5/4-x by linarith)
    nlinarith only [h4,hh,hl]
theorem solution (x : ℕ → ℝ) (hx : x 1=2)
    (h : ∀ n : ℕ, 1≤n → x (n+1)=(x n^4+9)/(10*x n)) :
    ∀ n : ℕ, 2≤n → 4/5<x n ∧ x n≤5/4 := by
  have h2 : x 2=5/4 := by rw [h 1 (by omega),hx]; norm_num
  intro n hn
  induction n,hn using Nat.le_induction with
  | base => norm_num [h2]
  | succ n hn ih => rw [h n (by omega)]; exact invariant (x n) ih.1 ih.2
example : (∀ (x : ℕ → ℝ) (hx : x 1=2)
    (h : ∀ n : ℕ, 1≤n → x (n+1)=(x n^4+9)/(10*x n)),
    ∀ n : ℕ, 2≤n → 4/5<x n ∧ x n≤5/4) := @solution
#print axioms solution
