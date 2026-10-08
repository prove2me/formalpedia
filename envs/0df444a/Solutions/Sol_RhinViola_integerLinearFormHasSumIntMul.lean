-- Prove2me | solution 1 for RhinViola.integerLinearFormHasSumIntMul
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T09:24:21.575589+00:00
-- url     : https://prove2.me/submissions/aaf7de86-82f5-4837-a20a-e307215e3bea

import Mathlib.Tactic

theorem solution
    (α : ℝ) (f : ℕ → ℝ) (r z c : ℤ)
    (hf : HasSum f ((z : ℝ) + (c : ℝ) * α)) :
    HasSum (fun k : ℕ => (r : ℝ) * f k)
      (((r * z : ℤ) : ℝ) + (((r * c : ℤ) : ℝ) * α)) := by
  have hsum :
      (r : ℝ) * ((z : ℝ) + (c : ℝ) * α) =
        (((r * z : ℤ) : ℝ) + (((r * c : ℤ) : ℝ) * α)) := by
    push_cast
    ring
  rw [← hsum]
  exact hf.mul_left (r : ℝ)
