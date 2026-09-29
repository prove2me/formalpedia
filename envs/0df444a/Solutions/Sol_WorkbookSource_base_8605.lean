-- Prove2me | solution 1 for WorkbookSource.base_8605
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:23:08.04407+00:00
-- url     : https://prove2.me/submissions/c7406757-2207-4971-a919-7acbe52fb3ca

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :  (a * b + b * c + c * a) * (a ^ 3 * b ^ 3 + b ^ 3 * c ^ 3 + c ^ 3 * a ^ 3) ≥ (-a + b + c) * (a - b + c) * (a + b - c) * (a ^ 3 + b ^ 3 + c ^ 3) * (a ^ 2 + b ^ 2 + c ^ 2) := by
  have haux (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^8 - a^7*b - a^7*c + 2*a^6*b*c + a^5*b^3 - 2*a^5*b^2*c - 2*a^5*b*c^2 + a^5*c^3 - a^4*b^4 + 2*a^4*b^3*c - 2*a^4*b^2*c^2 + 2*a^4*b*c^3 - a^4*c^4 + a^3*b^5 + 2*a^3*b^4*c + 2*a^3*b*c^4 + a^3*c^5 - 2*a^2*b^5*c - 2*a^2*b^4*c^2 - 2*a^2*b^2*c^4 - 2*a^2*b*c^5 - a*b^7 + 2*a*b^6*c - 2*a*b^5*c^2 + 2*a*b^4*c^3 + 2*a*b^3*c^4 - 2*a*b^2*c^5 + 2*a*b*c^6 - a*c^7 + b^8 - b^7*c + b^5*c^3 - b^4*c^4 + b^3*c^5 - b*c^7 + c^8) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (6 : ℝ) * a^6 * (b - a)^2 + (6 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (6 : ℝ) * a^6 * (c - b)^2 + (24 : ℝ) * a^5 * (b - a)^3 + (36 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (36 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (12 : ℝ) * a^5 * (c - b)^3 + (50 : ℝ) * a^4 * (b - a)^4 + (100 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (120 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (70 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (20 : ℝ) * a^4 * (c - b)^4 + (56 : ℝ) * a^3 * (b - a)^5 + (140 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (216 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (184 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (100 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (24 : ℝ) * a^3 * (c - b)^5 + (34 : ℝ) * a^2 * (b - a)^6 + (102 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (201 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (232 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (183 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (84 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (16 : ℝ) * a^2 * (c - b)^6 + (10 : ℝ) * a^1 * (b - a)^7 + (35 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (89 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (135 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (143 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (97 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (37 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (6 : ℝ) * a^1 * (c - b)^7 + (1 : ℝ) * (b - a)^8 + (4 : ℝ) * (b - a)^7 * (c - b)^1 + (14 : ℝ) * (b - a)^6 * (c - b)^2 + (28 : ℝ) * (b - a)^5 * (c - b)^3 + (39 : ℝ) * (b - a)^4 * (c - b)^4 + (36 : ℝ) * (b - a)^3 * (c - b)^5 + (21 : ℝ) * (b - a)^2 * (c - b)^6 + (7 : ℝ) * (b - a)^1 * (c - b)^7 + (1 : ℝ) * (c - b)^8 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^8 - a^7*b - a^7*c + 2*a^6*b*c + a^5*b^3 - 2*a^5*b^2*c - 2*a^5*b*c^2 + a^5*c^3 - a^4*b^4 + 2*a^4*b^3*c - 2*a^4*b^2*c^2 + 2*a^4*b*c^3 - a^4*c^4 + a^3*b^5 + 2*a^3*b^4*c + 2*a^3*b*c^4 + a^3*c^5 - 2*a^2*b^5*c - 2*a^2*b^4*c^2 - 2*a^2*b^2*c^4 - 2*a^2*b*c^5 - a*b^7 + 2*a*b^6*c - 2*a*b^5*c^2 + 2*a*b^4*c^3 + 2*a*b^3*c^4 - 2*a*b^2*c^5 + 2*a*b*c^6 - a*c^7 + b^8 - b^7*c + b^5*c^3 - b^4*c^4 + b^3*c^5 - b*c^7 + c^8) := by
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
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a * b + b * c + c * a) * (a ^ 3 * b ^ 3 + b ^ 3 * c ^ 3 + c ^ 3 * a ^ 3) ≥ (-a + b + c) * (a - b + c) * (a + b - c) * (a ^ 3 + b ^ 3 + c ^ 3) * (a ^ 2 + b ^ 2 + c ^ 2)) := @solution
#print axioms solution
