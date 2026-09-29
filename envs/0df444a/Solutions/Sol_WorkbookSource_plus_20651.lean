-- Prove2me | solution 1 for WorkbookSource.plus_20651
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T14:32:21.208546+00:00
-- url     : https://prove2.me/submissions/b0ed0dd1-9b3c-46fe-b46c-aa5eaa26b2ed

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
private lemma step (s x : ℝ) (hs : 0<s) (hx : s≤x) :
    s≤(x+s^2/x)/2 ∧ (x+s^2/x)/2-s≤(x-s)/2 := by
  have hp : 0<x := lt_of_lt_of_le hs hx
  have he : s^2/x*x=s^2 := div_mul_cancel₀ _ (ne_of_gt hp)
  constructor
  · have hh := sq_nonneg (x-s)
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    nlinarith only [he,hh,hp]
  · have hh := mul_nonneg (le_of_lt hs) (sub_nonneg.mpr hx)
    have hi : s^2/x ≤ s := (div_le_iff₀ hp).mpr (by nlinarith only [hh])
    linarith only [hi]
theorem solution (x : ℕ → ℝ) (h0 : x 0=1000)
    (h : ∀ n, x (n+1)=1/2*(x n+2002/x n)) : x 30<1/(10^6)+Real.sqrt 2002 := by
  let s := Real.sqrt 2002
  have hs : 0<s := by dsimp [s]; positivity
  have hs2 : s^2=2002 := Real.sq_sqrt (by norm_num)
  have hb : ∀ n : ℕ, s≤x n ∧ x n-s≤1000/(2:ℝ)^n := by
    intro n
    induction n with
    | zero => rw [h0]; norm_num; constructor <;> nlinarith only [hs,hs2]
    | succ n ih =>
      have hh := step s (x n) hs ih.1
      rw [hs2] at hh
      rw [h n]
      constructor
      · nlinarith only [hh.1]
      · have he : 1000/(2:ℝ)^(n+1)=(1000/(2:ℝ)^n)/2 := by rw [pow_succ]; ring
        rw [he]
        nlinarith only [hh.2,ih.2]
  have hh := (hb 30).2
  norm_num at hh ⊢
  dsimp [s] at hh
  linarith only [hh]
example : (∀ (x : ℕ → ℝ) (h0 : x 0=1000)
    (h : ∀ n, x (n+1)=1/2*(x n+2002/x n)), x 30<1/(10^6)+Real.sqrt 2002) := @solution
#print axioms solution
