-- Prove2me | solution 1 for WorkbookSource.base_29412
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:19:10.765525+00:00
-- url     : https://prove2.me/submissions/a661666c-7bf1-4456-a0c9-cb314cce3e39

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + 2 * b) * (b + 2 * c) * (c + 2 * a) / (2 * a + b + c) / (2 * b + c + a) / (2 * c + a + b) + 5 / 64 ≥ (a * b + b * c + c * a) / (2 * (a ^ 2 + b ^ 2 + c ^ 2))  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (10*a^5 + 99*a^4*b + 227*a^4*c + 77*a^3*b^2 + 144*a^3*b*c - 51*a^3*c^2 - 51*a^2*b^3 - 506*a^2*b^2*c - 506*a^2*b*c^2 + 77*a^2*c^3 + 227*a*b^4 + 144*a*b^3*c - 506*a*b^2*c^2 + 144*a*b*c^3 + 99*a*c^4 + 10*b^5 + 99*b^4*c + 77*b^3*c^2 - 51*b^2*c^3 + 227*b*c^4 + 10*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (1580 : ℝ) * a^3 * (b - a)^2 + (1580 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (1580 : ℝ) * a^3 * (c - b)^2 + (3166 : ℝ) * a^2 * (b - a)^3 + (4941 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (4923 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (1574 : ℝ) * a^2 * (c - b)^3 + (1968 : ℝ) * a^1 * (b - a)^4 + (4192 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (4678 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (2454 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (376 : ℝ) * a^1 * (c - b)^4 + (372 : ℝ) * (b - a)^5 + (1058 : ℝ) * (b - a)^4 * (c - b)^1 + (1386 : ℝ) * (b - a)^3 * (c - b)^2 + (957 : ℝ) * (b - a)^2 * (c - b)^3 + (277 : ℝ) * (b - a)^1 * (c - b)^4 + (10 : ℝ) * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (10*a^5 + 99*a^4*b + 227*a^4*c + 77*a^3*b^2 + 144*a^3*b*c - 51*a^3*c^2 - 51*a^2*b^3 - 506*a^2*b^2*c - 506*a^2*b*c^2 + 77*a^2*c^3 + 227*a*b^4 + 144*a*b^3*c - 506*a*b^2*c^2 + 144*a*b*c^3 + 99*a*c^4 + 10*b^5 + 99*b^4*c + 77*b^3*c^2 - 51*b^2*c^3 + 227*b*c^4 + 10*c^5) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (1580 : ℝ) * a^3 * (c - a)^2 + (1580 : ℝ) * a^3 * (c - a)^1 * (b - c)^1 + (1580 : ℝ) * a^3 * (b - c)^2 + (3166 : ℝ) * a^2 * (c - a)^3 + (4557 : ℝ) * a^2 * (c - a)^2 * (b - c)^1 + (4539 : ℝ) * a^2 * (c - a)^1 * (b - c)^2 + (1574 : ℝ) * a^2 * (b - c)^3 + (1968 : ℝ) * a^1 * (c - a)^4 + (3680 : ℝ) * a^1 * (c - a)^3 * (b - c)^1 + (3910 : ℝ) * a^1 * (c - a)^2 * (b - c)^2 + (2198 : ℝ) * a^1 * (c - a)^1 * (b - c)^3 + (376 : ℝ) * a^1 * (b - c)^4 + (372 : ℝ) * (c - a)^5 + (802 : ℝ) * (c - a)^4 * (b - c)^1 + (874 : ℝ) * (c - a)^3 * (b - c)^2 + (573 : ℝ) * (c - a)^2 * (b - c)^3 + (149 : ℝ) * (c - a)^1 * (b - c)^4 + (10 : ℝ) * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (10*a^5 + 99*a^4*b + 227*a^4*c + 77*a^3*b^2 + 144*a^3*b*c - 51*a^3*c^2 - 51*a^2*b^3 - 506*a^2*b^2*c - 506*a^2*b*c^2 + 77*a^2*c^3 + 227*a*b^4 + 144*a*b^3*c - 506*a*b^2*c^2 + 144*a*b*c^3 + 99*a*c^4 + 10*b^5 + 99*b^4*c + 77*b^3*c^2 - 51*b^2*c^3 + 227*b*c^4 + 10*c^5) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        convert haux0 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          convert haux1 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 c a b (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        convert haux1 b c a (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          convert haux0 b c a (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux1 c a b (by positivity) (by linarith) (by linarith) using 1 <;> ring
  have hn : 0 ≤ (10*a^5 + 99*a^4*b + 227*a^4*c + 77*a^3*b^2 + 144*a^3*b*c - 51*a^3*c^2 - 51*a^2*b^3 - 506*a^2*b^2*c - 506*a^2*b*c^2 + 77*a^2*c^3 + 227*a*b^4 + 144*a*b^3*c - 506*a*b^2*c^2 + 144*a*b*c^3 + 99*a*c^4 + 10*b^5 + 99*b^4*c + 77*b^3*c^2 - 51*b^2*c^3 + 227*b*c^4 + 10*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a + 2 * b) * (b + 2 * c) * (c + 2 * a) / (2 * a + b + c) / (2 * b + c + a) / (2 * c + a + b) + 5 / 64 ≥ (a * b + b * c + c * a) / (2 * (a ^ 2 + b ^ 2 + c ^ 2))) := @solution
#print axioms solution
