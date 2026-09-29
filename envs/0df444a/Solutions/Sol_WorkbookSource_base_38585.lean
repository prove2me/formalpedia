-- Prove2me | solution 1 for WorkbookSource.base_38585
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:44:55.620775+00:00
-- url     : https://prove2.me/submissions/3264c84b-7710-402c-be90-0b390e410a28

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) : (p^2 + q^2 + r^2) * (1 / p + 1 / q + 1 / r)^2 ≥ 27  := by
  have haux0 (p q r : ℝ) (hlow : 0 ≤ p) (hord1 : p ≤ q) (hord2 : q ≤ r) : 0 ≤ (p^4*q^2 + 2*p^4*q*r + p^4*r^2 + 2*p^3*q^2*r + 2*p^3*q*r^2 + p^2*q^4 + 2*p^2*q^3*r - 24*p^2*q^2*r^2 + 2*p^2*q*r^3 + p^2*r^4 + 2*p*q^4*r + 2*p*q^3*r^2 + 2*p*q^2*r^3 + 2*p*q*r^4 + q^4*r^2 + q^2*r^4) := by
    have hdiff1 : 0 ≤ (q - p) := by linarith
    have hdiff2 : 0 ≤ (r - q) := by linarith
    have hpos : 0 ≤ (18 : ℝ) * p^4 * (q - p)^2 + (18 : ℝ) * p^4 * (q - p)^1 * (r - q)^1 + (18 : ℝ) * p^4 * (r - q)^2 + (52 : ℝ) * p^3 * (q - p)^3 + (78 : ℝ) * p^3 * (q - p)^2 * (r - q)^1 + (66 : ℝ) * p^3 * (q - p)^1 * (r - q)^2 + (20 : ℝ) * p^3 * (r - q)^3 + (52 : ℝ) * p^2 * (q - p)^4 + (104 : ℝ) * p^2 * (q - p)^3 * (r - q)^1 + (90 : ℝ) * p^2 * (q - p)^2 * (r - q)^2 + (38 : ℝ) * p^2 * (q - p)^1 * (r - q)^3 + (4 : ℝ) * p^2 * (r - q)^4 + (20 : ℝ) * p^1 * (q - p)^5 + (50 : ℝ) * p^1 * (q - p)^4 * (r - q)^1 + (48 : ℝ) * p^1 * (q - p)^3 * (r - q)^2 + (22 : ℝ) * p^1 * (q - p)^2 * (r - q)^3 + (4 : ℝ) * p^1 * (q - p)^1 * (r - q)^4 + (2 : ℝ) * (q - p)^6 + (6 : ℝ) * (q - p)^5 * (r - q)^1 + (7 : ℝ) * (q - p)^4 * (r - q)^2 + (4 : ℝ) * (q - p)^3 * (r - q)^3 + (1 : ℝ) * (q - p)^2 * (r - q)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (p^4*q^2 + 2*p^4*q*r + p^4*r^2 + 2*p^3*q^2*r + 2*p^3*q*r^2 + p^2*q^4 + 2*p^2*q^3*r - 24*p^2*q^2*r^2 + 2*p^2*q*r^3 + p^2*r^4 + 2*p*q^4*r + 2*p*q^3*r^2 + 2*p*q^2*r^3 + 2*p*q*r^4 + q^4*r^2 + q^2*r^4) := by
    rcases le_total p q with hab | hba
    · rcases le_total q r with hbc | hcb
      ·
        convert haux0 p q r (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total p r with hac | hca
        ·
          convert haux0 p r q (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 r p q (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total p r with hbc | hcb
      ·
        convert haux0 q p r (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total q r with hac | hca
        ·
          convert haux0 q r p (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 r q p (by positivity) (by linarith) (by linarith) using 1 <;> ring
  have hn : 0 ≤ (p^4*q^2 + 2*p^4*q*r + p^4*r^2 + 2*p^3*q^2*r + 2*p^3*q*r^2 + p^2*q^4 + 2*p^2*q^3*r - 24*p^2*q^2*r^2 + 2*p^2*q*r^3 + p^2*r^4 + 2*p*q^4*r + 2*p*q^3*r^2 + 2*p*q^2*r^3 + 2*p*q*r^4 + q^4*r^2 + q^2*r^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r), (p^2 + q^2 + r^2) * (1 / p + 1 / q + 1 / r)^2 ≥ 27) := @solution
#print axioms solution
