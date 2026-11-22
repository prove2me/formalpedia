-- Prove2me | solution 1 for ParetoEFX296.Approx.three_inequalities
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-22T14:31:34.572023+00:00
-- url     : https://prove2.me/submissions/aab9ed19-a095-469f-b4c5-690c3eaf0619

import Mathlib

theorem solution (K : ℕ) (hK : 6 ≤ K) (α : ℝ) (hα : (2 : ℝ) / 3 + 1 / (K : ℝ) < α) :
    2 * (K : ℝ) + 3 < α * (3 * (K : ℝ)) ∧
    (K : ℝ) + 5 < α * (2 * (K : ℝ) + 2) ∧
    (K : ℝ) + 4 < α * (2 * (K : ℝ)) := by
  have hk : (6 : ℝ) ≤ K := by exact_mod_cast hK
  have kp : (0 : ℝ) < K := by linarith
  have ha : (0 : ℝ) < α := by
    have : 0 < (2 : ℝ) / 3 + 1 / K := by positivity
    linarith
  have hαk : 2 * (K : ℝ) / 3 + 1 < α * K := by
    have : (2 / 3 + 1 / (K : ℝ)) * K = 2 * K / 3 + 1 := by field_simp
    have ht := mul_lt_mul_of_pos_right hα kp
    linarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

#print axioms solution
