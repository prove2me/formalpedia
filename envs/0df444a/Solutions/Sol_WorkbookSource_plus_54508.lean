-- Prove2me | solution 1 for WorkbookSource.plus_54508
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T16:15:00.953552+00:00
-- url     : https://prove2.me/submissions/1da947e6-323c-41bf-9e6a-d2cbaf861e19

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem solution (a : ℕ → ℝ) (h0 : a 0=3)
    (h : ∀ n : ℕ, (3-a (n+1))*(6+a n)=18) :
    (∑ k ∈ Finset.range 13, 1/a k)=(16369:ℝ)/3 := by
  have hb : ∀ n : ℕ, 0 < a n ∧ 1/a n=((2:ℝ)^(n+1)-1)/3 := by
    intro n
    induction n with
    | zero => rw [h0]; norm_num
    | succ n ih =>
      have ha : 0 < a n := ih.1
      have hh := h n
      have hd : 0 < 6+a n := by linarith [ih.1]
      have he : a (n+1)=3*a n/(6+a n) := (eq_div_iff (ne_of_gt hd)).mpr (by nlinarith only [hh])
      have hp : 0 < a (n+1) := by rw [he]; positivity
      have hv : 1/a (n+1)=2*(1/a n)+1/3 := by
        field_simp [ne_of_gt ha,ne_of_gt hp]
        nlinarith only [hh]
      refine ⟨hp,?_⟩
      rw [hv,ih.2,pow_succ]
      ring
  have hv : ∀ n : ℕ, 1/a n=((2:ℝ)^(n+1)-1)/3 := fun n => (hb n).2
  simp_rw [hv]
  norm_num [Finset.sum_range_succ]
example : (∀ (a : ℕ → ℝ) (h0 : a 0=3)
    (h : ∀ n : ℕ, (3-a (n+1))*(6+a n)=18),
    (∑ k ∈ Finset.range 13, 1/a k)=(16369:ℝ)/3) := @solution
#print axioms solution
