-- Prove2me | solution 1 for TegmarkDimensionality.greens_radial_ode
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T01:25:08.91912+00:00
-- url     : https://prove2.me/submissions/565b4573-7482-4278-ae28-39f1938286db

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

open Real

theorem solution (n : ℕ) (hn : 2 < n) (r : ℝ) (hr : 0 < r) :
    let g := fun t : ℝ => t ^ ((2 : ℝ) - n)
    deriv (deriv g) r + ((n : ℝ) - 1) / r * deriv g r = 0 := by
  intro g
  have hrne : r ≠ 0 := ne_of_gt hr
  have hderiv : deriv g r = ((2 : ℝ) - n) * r ^ ((1 : ℝ) - n) := by
    simp only [g, Real.deriv_rpow_const]
    ring_nf
  have hderiv2 : deriv (deriv g) r = ((2 : ℝ) - n) * ((1 : ℝ) - n) * r ^ (-(n : ℝ)) := by
    have h1 : deriv g = fun t => ((2 : ℝ) - n) * t ^ ((1 : ℝ) - n) := by
      funext t
      simp only [g, Real.deriv_rpow_const]
      ring_nf
    rw [h1, deriv_const_mul]
    · rw [Real.deriv_rpow_const, mul_assoc]
      ring_nf
    · exact differentiableAt_rpow_const_of_ne ((1 : ℝ) - n) hrne
  rw [hderiv, hderiv2]
  have hsplit : r ^ ((1 : ℝ) - n) = r * r ^ (-(n : ℝ)) := by
    calc r ^ ((1 : ℝ) - n)
        = r ^ (1 + -(n : ℝ)) := by ring_nf
      _ = r ^ (1 : ℝ) * r ^ (-(n : ℝ)) := (Real.rpow_add hr) 1 (-(n : ℝ))
      _ = r * r ^ (-(n : ℝ)) := by simp
  field_simp [hrne]
  rw [hsplit]
  ring
