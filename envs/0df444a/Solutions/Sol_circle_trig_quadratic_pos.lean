-- Prove2me | solution 1 for circle_trig_quadratic_pos
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-28T17:31:16.749042+00:00
-- url     : https://prove2.me/submissions/31f7790b-119f-4784-80d5-57d822f500a1

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-- Positivity of a degree-two trigonometric polynomial on a circle, square-root free.
If `x² + y² = R²` and the second-harmonic amplitude is `S = √(p² + q²)`, then
`k + a x + b y + p (x² - y²) + 2 q x y > 0` as soon as `k - R² S > 0` and
`R² (a² + b²) < (k - R² S)²`. -/
theorem solution (x y R k a b p q S : ℝ)
    (hxy : x ^ 2 + y ^ 2 = R ^ 2) (hS : 0 ≤ S) (hS2 : S ^ 2 = p ^ 2 + q ^ 2)
    (h1 : 0 < k - R ^ 2 * S) (h2 : R ^ 2 * (a ^ 2 + b ^ 2) < (k - R ^ 2 * S) ^ 2) :
    0 < k + a * x + b * y + p * (x ^ 2 - y ^ 2) + 2 * q * x * y := by
  -- second harmonic: (pX + qY)² ≤ (p² + q²)(X² + Y²) = S² R⁴ with X = x² - y², Y = 2xy
  have hsec : -(R ^ 2 * S) ≤ p * (x ^ 2 - y ^ 2) + 2 * q * x * y := by
    have hsq : (p * (x ^ 2 - y ^ 2) + 2 * q * x * y) ^ 2 ≤ (R ^ 2 * S) ^ 2 := by
      have hXY : (x ^ 2 - y ^ 2) ^ 2 + (2 * x * y) ^ 2 = (R ^ 2) ^ 2 := by rw [← hxy]; ring
      nlinarith [sq_nonneg (p * (2 * x * y) - q * (x ^ 2 - y ^ 2))]
    have hRS : 0 ≤ R ^ 2 * S := by positivity
    nlinarith [sq_nonneg (p * (x ^ 2 - y ^ 2) + 2 * q * x * y + R ^ 2 * S)]
  -- first harmonic: (ax + by)² ≤ (a² + b²) R² < (k - R² S)²
  have hfst : -(k - R ^ 2 * S) < a * x + b * y := by
    have hsq : (a * x + b * y) ^ 2 < (k - R ^ 2 * S) ^ 2 := by
      nlinarith [sq_nonneg (a * y - b * x)]
    nlinarith [sq_nonneg (a * x + b * y + (k - R ^ 2 * S))]
  linarith
