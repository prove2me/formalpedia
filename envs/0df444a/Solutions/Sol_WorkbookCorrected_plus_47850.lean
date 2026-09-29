-- Prove2me | solution 1 for WorkbookCorrected.plus_47850
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T15:11:43.645229+00:00
-- url     : https://prove2.me/submissions/f129d2d2-051a-45b9-b4ba-190603b112b2

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem solution (a : ℕ → ℝ) (h1 : a 1=1/2)
    (h : ∀ n : ℕ, 1 ≤ n → a (n+1)=a n-(a n)^2) :
    ∀ n : ℕ, 1 ≤ n → 1 ≤ a n/a (n+1) ∧ a n/a (n+1) ≤ 2 := by
  have hb : ∀ n : ℕ, 0 < a (n+1) ∧ a (n+1) ≤ 1/2 := by
    intro n
    induction n with
    | zero => rw [h1]; norm_num
    | succ n ih =>
      rw [show n+1+1=(n+1)+1 by omega,h (n+1) (by omega)]
      have hp := mul_pos ih.1 (show 0 < 1-a (n+1) by linarith [ih.2])
      constructor
      · nlinarith only [hp]
      · nlinarith only [ih.2,sq_nonneg (a (n+1))]
  intro n hn
  obtain ⟨m,rfl⟩ : ∃ m : ℕ, n=m+1 := ⟨n-1,by omega⟩
  have hp := (hb (m+1)).1
  have hx := hb m
  have he := h (m+1) (by omega)
  constructor
  · apply (le_div_iff₀ hp).mpr
    nlinarith only [he,sq_nonneg (a (m+1))]
  · apply (div_le_iff₀ hp).mpr
    have hh := mul_nonneg (le_of_lt hx.1) (show 0 ≤ 1-2*a (m+1) by linarith [hx.2])
    nlinarith only [he,hh]
example : (∀ (a : ℕ → ℝ) (h1 : a 1=1/2)
    (h : ∀ n : ℕ, 1 ≤ n → a (n+1)=a n-(a n)^2),
    ∀ n : ℕ, 1 ≤ n → 1 ≤ a n/a (n+1) ∧ a n/a (n+1) ≤ 2) := @solution
#print axioms solution
