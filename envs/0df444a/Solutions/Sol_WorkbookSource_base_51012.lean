-- Prove2me | solution 1 for WorkbookSource.base_51012
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:35:36.293181+00:00
-- url     : https://prove2.me/submissions/29f75121-700d-42dc-b41e-42fe0f58b765

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * (a ^ 2 + 2 * b * c) / (b + 2 * c) ^ 2 + b * (b ^ 2 + 2 * a * c) / (c + 2 * a) ^ 2 + c * (c ^ 2 + 2 * a * b) / (a + 2 * b) ^ 2) ≥ (a + b + c) / 3  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (12*a^7 + 48*a^6*b + 12*a^6*c + 44*a^5*b^2 + 56*a^5*b*c - 13*a^5*c^2 - 20*a^4*b^3 + 56*a^4*b^2*c - 76*a^4*b*c^2 - 32*a^4*c^3 - 32*a^3*b^4 - 38*a^3*b^3*c - 49*a^3*b^2*c^2 - 38*a^3*b*c^3 - 20*a^3*c^4 - 13*a^2*b^5 - 76*a^2*b^4*c - 49*a^2*b^3*c^2 - 49*a^2*b^2*c^3 + 56*a^2*b*c^4 + 44*a^2*c^5 + 12*a*b^6 + 56*a*b^5*c + 56*a*b^4*c^2 - 38*a*b^3*c^3 - 76*a*b^2*c^4 + 56*a*b*c^5 + 48*a*c^6 + 12*b^7 + 48*b^6*c + 44*b^5*c^2 - 20*b^4*c^3 - 32*b^3*c^4 - 13*b^2*c^5 + 12*b*c^6 + 12*c^7) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (972 : ℝ) * a^5 * (b - a)^2 + (972 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (972 : ℝ) * a^5 * (c - b)^2 + (2835 : ℝ) * a^4 * (b - a)^3 + (3321 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (4536 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (2025 : ℝ) * a^4 * (c - b)^3 + (3303 : ℝ) * a^3 * (b - a)^4 + (4122 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (6993 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (6174 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (1683 : ℝ) * a^3 * (c - b)^4 + (1920 : ℝ) * a^2 * (b - a)^5 + (2298 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (4584 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (6441 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (3633 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (699 : ℝ) * a^2 * (c - b)^5 + (555 : ℝ) * a^1 * (b - a)^6 + (552 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (1236 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (2706 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (2433 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (966 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (144 : ℝ) * a^1 * (c - b)^6 + (63 : ℝ) * (b - a)^7 + (39 : ℝ) * (b - a)^6 * (c - b)^1 + (94 : ℝ) * (b - a)^5 * (c - b)^2 + (382 : ℝ) * (b - a)^4 * (c - b)^3 + (503 : ℝ) * (b - a)^3 * (c - b)^4 + (311 : ℝ) * (b - a)^2 * (c - b)^5 + (96 : ℝ) * (b - a)^1 * (c - b)^6 + (12 : ℝ) * (c - b)^7 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (12*a^7 + 48*a^6*b + 12*a^6*c + 44*a^5*b^2 + 56*a^5*b*c - 13*a^5*c^2 - 20*a^4*b^3 + 56*a^4*b^2*c - 76*a^4*b*c^2 - 32*a^4*c^3 - 32*a^3*b^4 - 38*a^3*b^3*c - 49*a^3*b^2*c^2 - 38*a^3*b*c^3 - 20*a^3*c^4 - 13*a^2*b^5 - 76*a^2*b^4*c - 49*a^2*b^3*c^2 - 49*a^2*b^2*c^3 + 56*a^2*b*c^4 + 44*a^2*c^5 + 12*a*b^6 + 56*a*b^5*c + 56*a*b^4*c^2 - 38*a*b^3*c^3 - 76*a*b^2*c^4 + 56*a*b*c^5 + 48*a*c^6 + 12*b^7 + 48*b^6*c + 44*b^5*c^2 - 20*b^4*c^3 - 32*b^3*c^4 - 13*b^2*c^5 + 12*b*c^6 + 12*c^7) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (972 : ℝ) * a^5 * (c - a)^2 + (972 : ℝ) * a^5 * (c - a)^1 * (b - c)^1 + (972 : ℝ) * a^5 * (b - c)^2 + (2835 : ℝ) * a^4 * (c - a)^3 + (5184 : ℝ) * a^4 * (c - a)^2 * (b - c)^1 + (6399 : ℝ) * a^4 * (c - a)^1 * (b - c)^2 + (2025 : ℝ) * a^4 * (b - c)^3 + (3303 : ℝ) * a^3 * (c - a)^4 + (9090 : ℝ) * a^3 * (c - a)^3 * (b - c)^1 + (14445 : ℝ) * a^3 * (c - a)^2 * (b - c)^2 + (8658 : ℝ) * a^3 * (c - a)^1 * (b - c)^3 + (1683 : ℝ) * a^3 * (b - c)^4 + (1920 : ℝ) * a^2 * (c - a)^5 + (7302 : ℝ) * a^2 * (c - a)^4 * (b - c)^1 + (14592 : ℝ) * a^2 * (c - a)^3 * (b - c)^2 + (12723 : ℝ) * a^2 * (c - a)^2 * (b - c)^3 + (4911 : ℝ) * a^2 * (c - a)^1 * (b - c)^4 + (699 : ℝ) * a^2 * (b - c)^5 + (555 : ℝ) * a^1 * (c - a)^6 + (2778 : ℝ) * a^1 * (c - a)^5 * (b - c)^1 + (6801 : ℝ) * a^1 * (c - a)^4 * (b - c)^2 + (7818 : ℝ) * a^1 * (c - a)^3 * (b - c)^3 + (4536 : ℝ) * a^1 * (c - a)^2 * (b - c)^4 + (1296 : ℝ) * a^1 * (c - a)^1 * (b - c)^5 + (144 : ℝ) * a^1 * (b - c)^6 + (63 : ℝ) * (c - a)^7 + (402 : ℝ) * (c - a)^6 * (b - c)^1 + (1183 : ℝ) * (c - a)^5 * (b - c)^2 + (1708 : ℝ) * (c - a)^4 * (b - c)^3 + (1340 : ℝ) * (c - a)^3 * (b - c)^4 + (584 : ℝ) * (c - a)^2 * (b - c)^5 + (132 : ℝ) * (c - a)^1 * (b - c)^6 + (12 : ℝ) * (b - c)^7 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (12*a^7 + 48*a^6*b + 12*a^6*c + 44*a^5*b^2 + 56*a^5*b*c - 13*a^5*c^2 - 20*a^4*b^3 + 56*a^4*b^2*c - 76*a^4*b*c^2 - 32*a^4*c^3 - 32*a^3*b^4 - 38*a^3*b^3*c - 49*a^3*b^2*c^2 - 38*a^3*b*c^3 - 20*a^3*c^4 - 13*a^2*b^5 - 76*a^2*b^4*c - 49*a^2*b^3*c^2 - 49*a^2*b^2*c^3 + 56*a^2*b*c^4 + 44*a^2*c^5 + 12*a*b^6 + 56*a*b^5*c + 56*a*b^4*c^2 - 38*a*b^3*c^3 - 76*a*b^2*c^4 + 56*a*b*c^5 + 48*a*c^6 + 12*b^7 + 48*b^6*c + 44*b^5*c^2 - 20*b^4*c^3 - 32*b^3*c^4 - 13*b^2*c^5 + 12*b*c^6 + 12*c^7) := by
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
  have hn : 0 ≤ (12*a^7 + 48*a^6*b + 12*a^6*c + 44*a^5*b^2 + 56*a^5*b*c - 13*a^5*c^2 - 20*a^4*b^3 + 56*a^4*b^2*c - 76*a^4*b*c^2 - 32*a^4*c^3 - 32*a^3*b^4 - 38*a^3*b^3*c - 49*a^3*b^2*c^2 - 38*a^3*b*c^3 - 20*a^3*c^4 - 13*a^2*b^5 - 76*a^2*b^4*c - 49*a^2*b^3*c^2 - 49*a^2*b^2*c^3 + 56*a^2*b*c^4 + 44*a^2*c^5 + 12*a*b^6 + 56*a*b^5*c + 56*a*b^4*c^2 - 38*a*b^3*c^3 - 76*a*b^2*c^4 + 56*a*b*c^5 + 48*a*c^6 + 12*b^7 + 48*b^6*c + 44*b^5*c^2 - 20*b^4*c^3 - 32*b^3*c^4 - 13*b^2*c^5 + 12*b*c^6 + 12*c^7) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a * (a ^ 2 + 2 * b * c) / (b + 2 * c) ^ 2 + b * (b ^ 2 + 2 * a * c) / (c + 2 * a) ^ 2 + c * (c ^ 2 + 2 * a * b) / (a + 2 * b) ^ 2) ≥ (a + b + c) / 3) := @solution
#print axioms solution
