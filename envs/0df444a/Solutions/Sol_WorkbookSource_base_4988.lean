-- Prove2me | solution 1 for WorkbookSource.base_4988
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:23:07.320625+00:00
-- url     : https://prove2.me/submissions/c16536ae-3533-4fa4-89d2-34d7ced106dd

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c: ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : (a + b + c) ^ 8 ≥ 128 * (a ^ 5 * b ^ 3 + a ^ 5 * c ^ 3 + b ^ 5 * a ^ 3 + b ^ 5 * c ^ 3 + c ^ 5 * a ^ 3 + c ^ 5 * b ^ 3)  := by
  have haux (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^8 + 8*a^7*b + 8*a^7*c + 28*a^6*b^2 + 56*a^6*b*c + 28*a^6*c^2 - 72*a^5*b^3 + 168*a^5*b^2*c + 168*a^5*b*c^2 - 72*a^5*c^3 + 70*a^4*b^4 + 280*a^4*b^3*c + 420*a^4*b^2*c^2 + 280*a^4*b*c^3 + 70*a^4*c^4 - 72*a^3*b^5 + 280*a^3*b^4*c + 560*a^3*b^3*c^2 + 560*a^3*b^2*c^3 + 280*a^3*b*c^4 - 72*a^3*c^5 + 28*a^2*b^6 + 168*a^2*b^5*c + 420*a^2*b^4*c^2 + 560*a^2*b^3*c^3 + 420*a^2*b^2*c^4 + 168*a^2*b*c^5 + 28*a^2*c^6 + 8*a*b^7 + 56*a*b^6*c + 168*a*b^5*c^2 + 280*a*b^4*c^3 + 280*a*b^3*c^4 + 168*a*b^2*c^5 + 56*a*b*c^6 + 8*a*c^7 + b^8 + 8*b^7*c + 28*b^6*c^2 - 72*b^5*c^3 + 70*b^4*c^4 - 72*b^3*c^5 + 28*b^2*c^6 + 8*b*c^7 + c^8) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (5793 : ℝ) * a^8 + (30896 : ℝ) * a^7 * (b - a)^1 + (15448 : ℝ) * a^7 * (c - b)^1 + (71152 : ℝ) * a^6 * (b - a)^2 + (71152 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (17084 : ℝ) * a^6 * (c - b)^2 + (91712 : ℝ) * a^5 * (b - a)^3 + (137568 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (67440 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (10792 : ℝ) * a^5 * (c - b)^3 + (71520 : ℝ) * a^4 * (b - a)^4 + (143040 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (107280 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (35760 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (4390 : ℝ) * a^4 * (c - b)^4 + (33792 : ℝ) * a^3 * (b - a)^5 + (84480 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (86400 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (45120 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (11920 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (1256 : ℝ) * a^3 * (c - b)^5 + (8960 : ℝ) * a^2 * (b - a)^6 + (26880 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (35520 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (26240 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (11280 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (2640 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (252 : ℝ) * a^2 * (c - b)^6 + (1024 : ℝ) * a^1 * (b - a)^7 + (3584 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (6144 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (6400 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (4160 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (1632 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (336 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (24 : ℝ) * a^1 * (c - b)^7 + (128 : ℝ) * (b - a)^6 * (c - b)^2 + (384 : ℝ) * (b - a)^5 * (c - b)^3 + (480 : ℝ) * (b - a)^4 * (c - b)^4 + (320 : ℝ) * (b - a)^3 * (c - b)^5 + (112 : ℝ) * (b - a)^2 * (c - b)^6 + (16 : ℝ) * (b - a)^1 * (c - b)^7 + (1 : ℝ) * (c - b)^8 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^8 + 8*a^7*b + 8*a^7*c + 28*a^6*b^2 + 56*a^6*b*c + 28*a^6*c^2 - 72*a^5*b^3 + 168*a^5*b^2*c + 168*a^5*b*c^2 - 72*a^5*c^3 + 70*a^4*b^4 + 280*a^4*b^3*c + 420*a^4*b^2*c^2 + 280*a^4*b*c^3 + 70*a^4*c^4 - 72*a^3*b^5 + 280*a^3*b^4*c + 560*a^3*b^3*c^2 + 560*a^3*b^2*c^3 + 280*a^3*b*c^4 - 72*a^3*c^5 + 28*a^2*b^6 + 168*a^2*b^5*c + 420*a^2*b^4*c^2 + 560*a^2*b^3*c^3 + 420*a^2*b^2*c^4 + 168*a^2*b*c^5 + 28*a^2*c^6 + 8*a*b^7 + 56*a*b^6*c + 168*a*b^5*c^2 + 280*a*b^4*c^3 + 280*a*b^3*c^4 + 168*a*b^2*c^5 + 56*a*b*c^6 + 8*a*c^7 + b^8 + 8*b^7*c + 28*b^6*c^2 - 72*b^5*c^3 + 70*b^4*c^4 - 72*b^3*c^5 + 28*b^2*c^6 + 8*b*c^7 + c^8) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        convert haux a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          convert haux a c b (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux c a b (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        convert haux b a c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          convert haux b c a (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux c b a (by positivity) (by linarith) (by linarith) using 1 <;> ring
  nlinarith only [hp]
example : (∀ (a b c: ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0), (a + b + c) ^ 8 ≥ 128 * (a ^ 5 * b ^ 3 + a ^ 5 * c ^ 3 + b ^ 5 * a ^ 3 + b ^ 5 * c ^ 3 + c ^ 5 * a ^ 3 + c ^ 5 * b ^ 3)) := @solution
#print axioms solution
