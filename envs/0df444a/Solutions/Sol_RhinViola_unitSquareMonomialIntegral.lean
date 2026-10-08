-- Prove2me | solution 1 for RhinViola.unitSquareMonomialIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T11:24:56.448393+00:00
-- url     : https://prove2.me/submissions/0fcdcab5-8986-4c89-9f5a-b2d57f496003

import Theorems.Thm_RhinViola_unitIntervalMonomialIntegral
import Mathlib.Tactic

theorem solution (a b : ℕ) :
    (∫ x : ℝ in (0 : ℝ)..1,
      ∫ y : ℝ in (0 : ℝ)..1, x ^ a * y ^ b) =
      ((1 : ℝ) / (((a + 1 : ℕ) : ℝ))) *
        ((1 : ℝ) / (((b + 1 : ℕ) : ℝ))) := by
  calc
    (∫ x : ℝ in (0 : ℝ)..1,
        ∫ y : ℝ in (0 : ℝ)..1, x ^ a * y ^ b) =
      ∫ x : ℝ in (0 : ℝ)..1,
        x ^ a * ((1 : ℝ) / (((b + 1 : ℕ) : ℝ))) := by
      apply intervalIntegral.integral_congr
      intro x hx
      change (∫ y : ℝ in (0 : ℝ)..1, x ^ a * y ^ b) =
        x ^ a * ((1 : ℝ) / (((b + 1 : ℕ) : ℝ)))
      rw [intervalIntegral.integral_const_mul,
        RhinViola.unitIntervalMonomialIntegral]
    _ =
      (∫ x : ℝ in (0 : ℝ)..1, x ^ a) *
        ((1 : ℝ) / (((b + 1 : ℕ) : ℝ))) := by
      rw [intervalIntegral.integral_mul_const]
    _ =
      ((1 : ℝ) / (((a + 1 : ℕ) : ℝ))) *
        ((1 : ℝ) / (((b + 1 : ℕ) : ℝ))) := by
      rw [RhinViola.unitIntervalMonomialIntegral]
