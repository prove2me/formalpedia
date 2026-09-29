-- Prove2me | solution 1 for WorkbookCorrected.plus_66265
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T13:51:16.034185+00:00
-- url     : https://prove2.me/submissions/434286f3-45e2-4ee6-8788-6f548cfd6325

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
private lemma formula (a : ℕ → ℝ) (h0 : a 1 = 3)
    (h : ∀ m n : ℕ, n ≤ m → a (m+n)+a (m-n)-(m:ℝ)+(n:ℝ)-1 = 1/2*(a (2*m)+a (2*n))) :
    ∀ n : ℕ, a n = (n:ℝ)^2+n+1 := by
  have hz := h 0 0 (by omega)
  norm_num at hz
  have hzero : a 0 = 1 := by linarith only [hz]
  have hd (m : ℕ) : a (2*m) = 4*a m-2*(m:ℝ)-3 := by
    have hh := h m 0 (by omega)
    simp only [Nat.add_zero,Nat.sub_zero,Nat.mul_zero,Nat.cast_zero,hzero] at hh
    linarith only [hh]
  have htwo : a 2 = 7 := by
    have hh := hd 1
    norm_num [h0] at hh
    exact hh
  intro n
  induction n using Nat.twoStepInduction with
  | zero => simpa using hzero
  | one => norm_num [h0]
  | more n hn hn1 =>
    have hh := h (n+1) 1 (by omega)
    have hdn := hd (n+1)
    have hi : n+1-1=n := by omega
    simp only [hi,htwo,Nat.mul_one,Nat.cast_add,Nat.cast_one] at hh hdn
    norm_num only [Nat.cast_add,Nat.cast_ofNat] at hn1 ⊢
    nlinarith only [hh,hdn,hn,hn1]
theorem solution (a : ℕ → ℝ) (h0 : a 1 = 3)
    (h : ∀ m n : ℕ, n ≤ m → a (m+n)+a (m-n)-(m:ℝ)+(n:ℝ)-1 = 1/2*(a (2*m)+a (2*n))) : a 2004 = 4018021 := by
  have hh := formula a h0 h 2004
  norm_num at hh
  exact hh
example : (∀ (a : ℕ → ℝ) (h0 : a 1 = 3)
    (h : ∀ m n : ℕ, n ≤ m → a (m+n)+a (m-n)-(m:ℝ)+(n:ℝ)-1 = 1/2*(a (2*m)+a (2*n))), a 2004 = 4018021) := @solution
#print axioms solution
