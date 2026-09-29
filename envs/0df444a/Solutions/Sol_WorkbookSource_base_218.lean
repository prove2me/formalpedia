-- Prove2me | solution 1 for WorkbookSource.base_218
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:44:28.911627+00:00
-- url     : https://prove2.me/submissions/008daa18-bf69-4bdc-956c-8110d305f5be

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * (b + c) / (a ^ 2 + 2 * b * c) + b * (c + a) / (b ^ 2 + 2 * c * a) + c * (a + b) / (c ^ 2 + 2 * a * b) + 1) ≤ (a + b + c) ^ 2 / (a * b + b * c + a * c)  := by
  have haux (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^6*b*c + 2*a^5*b^2*c + 2*a^5*b*c^2 + 2*a^4*b^4 - 3*a^4*b^3*c - a^4*b^2*c^2 - 3*a^4*b*c^3 + 2*a^4*c^4 - 3*a^3*b^4*c - 3*a^3*b^3*c^2 - 3*a^3*b^2*c^3 - 3*a^3*b*c^4 + 2*a^2*b^5*c - a^2*b^4*c^2 - 3*a^2*b^3*c^3 - a^2*b^2*c^4 + 2*a^2*b*c^5 + 4*a*b^6*c + 2*a*b^5*c^2 - 3*a*b^4*c^3 - 3*a*b^3*c^4 + 2*a*b^2*c^5 + 4*a*b*c^6 + 2*b^4*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (45 : ℝ) * a^6 * (b - a)^2 + (45 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (45 : ℝ) * a^6 * (c - b)^2 + (174 : ℝ) * a^5 * (b - a)^3 + (261 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (279 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (96 : ℝ) * a^5 * (c - b)^3 + (272 : ℝ) * a^4 * (b - a)^4 + (544 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (666 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (394 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (77 : ℝ) * a^4 * (c - b)^4 + (220 : ℝ) * a^3 * (b - a)^5 + (550 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (776 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (614 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (224 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (28 : ℝ) * a^3 * (c - b)^5 + (97 : ℝ) * a^2 * (b - a)^6 + (291 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (459 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (433 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (222 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (54 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (4 : ℝ) * a^2 * (c - b)^6 + (22 : ℝ) * a^1 * (b - a)^7 + (77 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (127 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (125 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (75 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (26 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (4 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (2 : ℝ) * (b - a)^8 + (8 : ℝ) * (b - a)^7 * (c - b)^1 + (12 : ℝ) * (b - a)^6 * (c - b)^2 + (8 : ℝ) * (b - a)^5 * (c - b)^3 + (2 : ℝ) * (b - a)^4 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^6*b*c + 2*a^5*b^2*c + 2*a^5*b*c^2 + 2*a^4*b^4 - 3*a^4*b^3*c - a^4*b^2*c^2 - 3*a^4*b*c^3 + 2*a^4*c^4 - 3*a^3*b^4*c - 3*a^3*b^3*c^2 - 3*a^3*b^2*c^3 - 3*a^3*b*c^4 + 2*a^2*b^5*c - a^2*b^4*c^2 - 3*a^2*b^3*c^3 - a^2*b^2*c^4 + 2*a^2*b*c^5 + 4*a*b^6*c + 2*a*b^5*c^2 - 3*a*b^4*c^3 - 3*a*b^3*c^4 + 2*a*b^2*c^5 + 4*a*b*c^6 + 2*b^4*c^4) := by
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
  have hn : 0 ≤ (4*a^6*b*c + 2*a^5*b^2*c + 2*a^5*b*c^2 + 2*a^4*b^4 - 3*a^4*b^3*c - a^4*b^2*c^2 - 3*a^4*b*c^3 + 2*a^4*c^4 - 3*a^3*b^4*c - 3*a^3*b^3*c^2 - 3*a^3*b^2*c^3 - 3*a^3*b*c^4 + 2*a^2*b^5*c - a^2*b^4*c^2 - 3*a^2*b^3*c^3 - a^2*b^2*c^4 + 2*a^2*b*c^5 + 4*a*b^6*c + 2*a*b^5*c^2 - 3*a*b^4*c^3 - 3*a*b^3*c^4 + 2*a*b^2*c^5 + 4*a*b*c^6 + 2*b^4*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a * (b + c) / (a ^ 2 + 2 * b * c) + b * (c + a) / (b ^ 2 + 2 * c * a) + c * (a + b) / (c ^ 2 + 2 * a * b) + 1) ≤ (a + b + c) ^ 2 / (a * b + b * c + a * c)) := @solution
#print axioms solution
