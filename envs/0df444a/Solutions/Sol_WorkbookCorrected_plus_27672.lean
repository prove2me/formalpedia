-- Prove2me | solution 1 for WorkbookCorrected.plus_27672
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T13:12:57.954224+00:00
-- url     : https://prove2.me/submissions/12368fe2-1e20-47e5-8fee-4320a9439f07

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0<a ∧ a<1) (hb : 0<b ∧ b<1)
    (hc : 0<c ∧ c<1) (h : (a+b)*(b+c)=1) : b^2 ≥ (1-a)*(1-c) := by
  have he : 0 < a+c-2*a*c := by
    nlinarith only [mul_pos ha.1 (sub_pos.mpr hc.2),mul_pos hc.1 (sub_pos.mpr ha.2)]
  have hp : 0 ≤ a+c-a*c := by
    nlinarith only [mul_pos ha.1 (sub_pos.mpr hc.2),hc.1]
  have hd : 0 < a+c-2*a*c+b*(a+c)+(a+c)^2 := by
    nlinarith only [he,mul_pos hb.1 (add_pos ha.1 hc.1),sq_nonneg (a+c)]
  have hid : (b^2-(1-a)*(1-c))*(a+c-2*a*c+b*(a+c)+(a+c)^2) =
      (a-c)^2*(a+c-a*c) := by
    linear_combination (a+c-2*a*c+b*(a+c))*h
  have hn : 0 ≤ b^2-(1-a)*(1-c) := by
    by_contra hn
    have hn' : b^2-(1-a)*(1-c)<0 := lt_of_not_ge hn
    have hh := mul_neg_of_neg_of_pos hn' hd
    rw [hid] at hh
    exact (not_lt_of_ge (mul_nonneg (sq_nonneg (a-c)) hp)) hh
  linarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0<a ∧ a<1) (hb : 0<b ∧ b<1)
    (hc : 0<c ∧ c<1) (h : (a+b)*(b+c)=1), b^2 ≥ (1-a)*(1-c)) := @solution
#print axioms solution
