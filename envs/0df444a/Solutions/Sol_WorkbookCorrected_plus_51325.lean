-- Prove2me | solution 1 for WorkbookCorrected.plus_51325
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T15:16:25.030764+00:00
-- url     : https://prove2.me/submissions/df6a385b-18f7-4710-b5b1-1c87f7f3d9cf

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem solution (f : ℕ → ℝ → ℝ)
    (hf : ∀ n : ℕ, ∀ x : ℝ, f n x=if 0 ≤ x ∧ x ≤ 1/(n:ℝ) then Real.sqrt n else 0) :
    ¬ ∃ g : ℝ → ℝ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N < n →
      ∀ x ∈ Set.Icc (0:ℝ) 1, |f n x-g x| < ε := by
  rintro ⟨g,hg⟩
  obtain ⟨N,hN⟩ := hg 1 (by norm_num)
  obtain ⟨K,hK⟩ := exists_nat_gt ((|g 0|+2)^2)
  let n := N+K+1
  have hn : N < n := by dsimp [n]; omega
  have hh := hN n hn 0 (by norm_num)
  have he : f n 0=Real.sqrt n := by
    rw [hf n 0]
    simp only [le_refl,true_and]
    rw [if_pos (by positivity)]
  rw [he] at hh
  have hs := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n)
  have hs0 := Real.sqrt_nonneg (n:ℝ)
  have hb := (abs_lt.mp hh).2
  have ha := le_abs_self (g 0)
  have ha0 := abs_nonneg (g 0)
  have hkn : (K:ℝ) ≤ n := by exact_mod_cast (show K ≤ n by dsimp [n]; omega)
  have hp := mul_nonneg (show 0 ≤ |g 0|+2-Real.sqrt n by linarith)
    (show 0 ≤ |g 0|+2+Real.sqrt n by linarith)
  nlinarith only [hK,hkn,hs,hp]
example : (∀ (f : ℕ → ℝ → ℝ)
    (hf : ∀ n : ℕ, ∀ x : ℝ, f n x=if 0 ≤ x ∧ x ≤ 1/(n:ℝ) then Real.sqrt n else 0),
    ¬ ∃ g : ℝ → ℝ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N < n →
      ∀ x ∈ Set.Icc (0:ℝ) 1, |f n x-g x| < ε) := @solution
#print axioms solution
