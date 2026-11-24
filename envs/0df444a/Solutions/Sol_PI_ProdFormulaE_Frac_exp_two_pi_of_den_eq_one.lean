-- Prove2me | solution 1 for PI.ProdFormulaE.Frac.exp_two_pi_of_den_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T02:21:25.780362+00:00
-- url     : https://prove2.me/submissions/9362fc6f-5ab8-4923-bc78-a092edd185fa

import Mathlib


theorem solution {a : ℚ} (ha : a.den = 1) :
    Complex.exp (2 * Real.pi * Complex.I * (a : ℂ)) = 1 := by
  have h : (a : ℂ) = (a.num : ℂ) := by rw [Rat.cast_def,ha]; simp
  rw [h, mul_comm (2 * (Real.pi : ℂ) * Complex.I)]
  exact Complex.exp_int_mul_two_pi_mul_I _
