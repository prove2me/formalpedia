-- Prove2me | solution 1 for WorkbookSource.base_4130
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:11:37.701104+00:00
-- url     : https://prove2.me/submissions/5c36c85b-ee3f-4ab7-93e2-fd2b817114bb

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (a ^ 2 + b ^ 2) + 1 / (b ^ 2 + c ^ 2) + 1 / (c ^ 2 + a ^ 2) + 15 / (a + b + c) ^ 2) ≥ 6 / (a * b + b * c + c * a)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^7*b + a^7*c - 4*a^6*b^2 + 5*a^6*b*c - 4*a^6*c^2 + 7*a^5*b^3 + 11*a^5*b^2*c + 11*a^5*b*c^2 + 7*a^5*c^3 - 6*a^4*b^4 + 19*a^4*b^3*c - 10*a^4*b^2*c^2 + 19*a^4*b*c^3 - 6*a^4*c^4 + 7*a^3*b^5 + 19*a^3*b^4*c + 27*a^3*b^3*c^2 + 27*a^3*b^2*c^3 + 19*a^3*b*c^4 + 7*a^3*c^5 - 4*a^2*b^6 + 11*a^2*b^5*c - 10*a^2*b^4*c^2 + 27*a^2*b^3*c^3 - 10*a^2*b^2*c^4 + 11*a^2*b*c^5 - 4*a^2*c^6 + a*b^7 + 5*a*b^6*c + 11*a*b^5*c^2 + 19*a*b^4*c^3 + 19*a*b^3*c^4 + 11*a*b^2*c^5 + 5*a*b*c^6 + a*c^7 + b^7*c - 4*b^6*c^2 + 7*b^5*c^3 - 6*b^4*c^4 + 7*b^3*c^5 - 4*b^2*c^6 + b*c^7) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (252 : ℝ) * a^8 + (1344 : ℝ) * a^7 * (b - a)^1 + (672 : ℝ) * a^7 * (c - b)^1 + (3144 : ℝ) * a^6 * (b - a)^2 + (3144 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (792 : ℝ) * a^6 * (c - b)^2 + (4212 : ℝ) * a^5 * (b - a)^3 + (6318 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (3186 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (540 : ℝ) * a^5 * (c - b)^3 + (3521 : ℝ) * a^4 * (b - a)^4 + (7042 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (5313 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (1792 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (221 : ℝ) * a^4 * (c - b)^4 + (1856 : ℝ) * a^3 * (b - a)^5 + (4640 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (4656 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (2344 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (592 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (60 : ℝ) * a^3 * (c - b)^5 + (581 : ℝ) * a^2 * (b - a)^6 + (1743 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (2181 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (1457 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (561 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (123 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (11 : ℝ) * a^2 * (c - b)^6 + (88 : ℝ) * a^1 * (b - a)^7 + (308 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (460 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (380 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (200 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (74 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (18 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (2 : ℝ) * a^1 * (c - b)^7 + (2 : ℝ) * (b - a)^8 + (8 : ℝ) * (b - a)^7 * (c - b)^1 + (12 : ℝ) * (b - a)^6 * (c - b)^2 + (8 : ℝ) * (b - a)^5 * (c - b)^3 + (4 : ℝ) * (b - a)^4 * (c - b)^4 + (4 : ℝ) * (b - a)^3 * (c - b)^5 + (3 : ℝ) * (b - a)^2 * (c - b)^6 + (1 : ℝ) * (b - a)^1 * (c - b)^7 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^7*b + a^7*c - 4*a^6*b^2 + 5*a^6*b*c - 4*a^6*c^2 + 7*a^5*b^3 + 11*a^5*b^2*c + 11*a^5*b*c^2 + 7*a^5*c^3 - 6*a^4*b^4 + 19*a^4*b^3*c - 10*a^4*b^2*c^2 + 19*a^4*b*c^3 - 6*a^4*c^4 + 7*a^3*b^5 + 19*a^3*b^4*c + 27*a^3*b^3*c^2 + 27*a^3*b^2*c^3 + 19*a^3*b*c^4 + 7*a^3*c^5 - 4*a^2*b^6 + 11*a^2*b^5*c - 10*a^2*b^4*c^2 + 27*a^2*b^3*c^3 - 10*a^2*b^2*c^4 + 11*a^2*b*c^5 - 4*a^2*c^6 + a*b^7 + 5*a*b^6*c + 11*a*b^5*c^2 + 19*a*b^4*c^3 + 19*a*b^3*c^4 + 11*a*b^2*c^5 + 5*a*b*c^6 + a*c^7 + b^7*c - 4*b^6*c^2 + 7*b^5*c^3 - 6*b^4*c^4 + 7*b^3*c^5 - 4*b^2*c^6 + b*c^7) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        convert haux0 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          convert haux0 a c b (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 c a b (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        convert haux0 b a c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          convert haux0 b c a (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 c b a (by positivity) (by linarith) (by linarith) using 1 <;> ring
  have hn : 0 ≤ (a^7*b + a^7*c - 4*a^6*b^2 + 5*a^6*b*c - 4*a^6*c^2 + 7*a^5*b^3 + 11*a^5*b^2*c + 11*a^5*b*c^2 + 7*a^5*c^3 - 6*a^4*b^4 + 19*a^4*b^3*c - 10*a^4*b^2*c^2 + 19*a^4*b*c^3 - 6*a^4*c^4 + 7*a^3*b^5 + 19*a^3*b^4*c + 27*a^3*b^3*c^2 + 27*a^3*b^2*c^3 + 19*a^3*b*c^4 + 7*a^3*c^5 - 4*a^2*b^6 + 11*a^2*b^5*c - 10*a^2*b^4*c^2 + 27*a^2*b^3*c^3 - 10*a^2*b^2*c^4 + 11*a^2*b*c^5 - 4*a^2*c^6 + a*b^7 + 5*a*b^6*c + 11*a*b^5*c^2 + 19*a*b^4*c^3 + 19*a*b^3*c^4 + 11*a*b^2*c^5 + 5*a*b*c^6 + a*c^7 + b^7*c - 4*b^6*c^2 + 7*b^5*c^3 - 6*b^4*c^4 + 7*b^3*c^5 - 4*b^2*c^6 + b*c^7) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (1 / (a ^ 2 + b ^ 2) + 1 / (b ^ 2 + c ^ 2) + 1 / (c ^ 2 + a ^ 2) + 15 / (a + b + c) ^ 2) ≥ 6 / (a * b + b * c + c * a)) := @solution
#print axioms solution
