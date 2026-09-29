-- Prove2me | solution 1 for WorkbookSource.base_4630
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:13:25.721371+00:00
-- url     : https://prove2.me/submissions/350bc4f2-94ff-4cdf-823d-60b972a29d4f

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 1 / a + 1 / b + 1 / c + 5 / (3 * a + b) + 5 / (3 * b + c) + 5 / (3 * c + a) ≥ 9 / (a + 3 * b) + 9 / (b + 3 * c) + 9 / (c + 3 * a)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (27*a^5*b^3 - 81*a^5*b^2*c + 171*a^5*b*c^2 + 27*a^5*c^3 + 90*a^4*b^4 - 297*a^4*b^3*c - 90*a^4*b^2*c^2 + 543*a^4*b*c^3 + 90*a^4*c^4 + 27*a^3*b^5 + 543*a^3*b^4*c - 390*a^3*b^3*c^2 - 390*a^3*b^2*c^3 - 297*a^3*b*c^4 + 27*a^3*c^5 + 171*a^2*b^5*c - 90*a^2*b^4*c^2 - 390*a^2*b^3*c^3 - 90*a^2*b^2*c^4 - 81*a^2*b*c^5 - 81*a*b^5*c^2 - 297*a*b^4*c^3 + 543*a*b^3*c^4 + 171*a*b^2*c^5 + 27*b^5*c^3 + 90*b^4*c^4 + 27*b^3*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (1536 : ℝ) * a^6 * (b - a)^2 + (1536 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (1536 : ℝ) * a^6 * (c - b)^2 + (6912 : ℝ) * a^5 * (b - a)^3 + (12384 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (10080 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (2304 : ℝ) * a^5 * (c - b)^3 + (12576 : ℝ) * a^4 * (b - a)^4 + (31872 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (30528 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (11232 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (1056 : ℝ) * a^4 * (c - b)^4 + (11760 : ℝ) * a^3 * (b - a)^5 + (37590 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (44268 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (22092 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (3942 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (144 : ℝ) * a^3 * (c - b)^5 + (5904 : ℝ) * a^2 * (b - a)^6 + (21996 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (30735 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (19350 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (5049 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (342 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (1488 : ℝ) * a^1 * (b - a)^7 + (6006 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (9342 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (6870 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (2298 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (252 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (144 : ℝ) * (b - a)^8 + (576 : ℝ) * (b - a)^7 * (c - b)^1 + (891 : ℝ) * (b - a)^6 * (c - b)^2 + (657 : ℝ) * (b - a)^5 * (c - b)^3 + (225 : ℝ) * (b - a)^4 * (c - b)^4 + (27 : ℝ) * (b - a)^3 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (27*a^5*b^3 - 81*a^5*b^2*c + 171*a^5*b*c^2 + 27*a^5*c^3 + 90*a^4*b^4 - 297*a^4*b^3*c - 90*a^4*b^2*c^2 + 543*a^4*b*c^3 + 90*a^4*c^4 + 27*a^3*b^5 + 543*a^3*b^4*c - 390*a^3*b^3*c^2 - 390*a^3*b^2*c^3 - 297*a^3*b*c^4 + 27*a^3*c^5 + 171*a^2*b^5*c - 90*a^2*b^4*c^2 - 390*a^2*b^3*c^3 - 90*a^2*b^2*c^4 - 81*a^2*b*c^5 - 81*a*b^5*c^2 - 297*a*b^4*c^3 + 543*a*b^3*c^4 + 171*a*b^2*c^5 + 27*b^5*c^3 + 90*b^4*c^4 + 27*b^3*c^5) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (1536 : ℝ) * a^6 * (c - a)^2 + (1536 : ℝ) * a^6 * (c - a)^1 * (b - c)^1 + (1536 : ℝ) * a^6 * (b - c)^2 + (6912 : ℝ) * a^5 * (c - a)^3 + (8352 : ℝ) * a^5 * (c - a)^2 * (b - c)^1 + (6048 : ℝ) * a^5 * (c - a)^1 * (b - c)^2 + (2304 : ℝ) * a^5 * (b - c)^3 + (12576 : ℝ) * a^4 * (c - a)^4 + (18432 : ℝ) * a^4 * (c - a)^3 * (b - c)^1 + (10368 : ℝ) * a^4 * (c - a)^2 * (b - c)^2 + (4512 : ℝ) * a^4 * (c - a)^1 * (b - c)^3 + (1056 : ℝ) * a^4 * (b - c)^4 + (11760 : ℝ) * a^3 * (c - a)^5 + (21210 : ℝ) * a^3 * (c - a)^4 * (b - c)^1 + (11508 : ℝ) * a^3 * (c - a)^3 * (b - c)^2 + (2772 : ℝ) * a^3 * (c - a)^2 * (b - c)^3 + (1002 : ℝ) * a^3 * (c - a)^1 * (b - c)^4 + (144 : ℝ) * a^3 * (b - c)^5 + (5904 : ℝ) * a^2 * (c - a)^6 + (13428 : ℝ) * a^2 * (c - a)^5 * (b - c)^1 + (9315 : ℝ) * a^2 * (c - a)^4 * (b - c)^2 + (1710 : ℝ) * a^2 * (c - a)^3 * (b - c)^3 + (9 : ℝ) * a^2 * (c - a)^2 * (b - c)^4 + (90 : ℝ) * a^2 * (c - a)^1 * (b - c)^5 + (1488 : ℝ) * a^1 * (c - a)^7 + (4410 : ℝ) * a^1 * (c - a)^6 * (b - c)^1 + (4554 : ℝ) * a^1 * (c - a)^5 * (b - c)^2 + (1830 : ℝ) * a^1 * (c - a)^4 * (b - c)^3 + (198 : ℝ) * a^1 * (c - a)^3 * (b - c)^4 + (144 : ℝ) * (c - a)^8 + (576 : ℝ) * (c - a)^7 * (b - c)^1 + (891 : ℝ) * (c - a)^6 * (b - c)^2 + (657 : ℝ) * (c - a)^5 * (b - c)^3 + (225 : ℝ) * (c - a)^4 * (b - c)^4 + (27 : ℝ) * (c - a)^3 * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (27*a^5*b^3 - 81*a^5*b^2*c + 171*a^5*b*c^2 + 27*a^5*c^3 + 90*a^4*b^4 - 297*a^4*b^3*c - 90*a^4*b^2*c^2 + 543*a^4*b*c^3 + 90*a^4*c^4 + 27*a^3*b^5 + 543*a^3*b^4*c - 390*a^3*b^3*c^2 - 390*a^3*b^2*c^3 - 297*a^3*b*c^4 + 27*a^3*c^5 + 171*a^2*b^5*c - 90*a^2*b^4*c^2 - 390*a^2*b^3*c^3 - 90*a^2*b^2*c^4 - 81*a^2*b*c^5 - 81*a*b^5*c^2 - 297*a*b^4*c^3 + 543*a*b^3*c^4 + 171*a*b^2*c^5 + 27*b^5*c^3 + 90*b^4*c^4 + 27*b^3*c^5) := by
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
  have hn : 0 ≤ (27*a^5*b^3 - 81*a^5*b^2*c + 171*a^5*b*c^2 + 27*a^5*c^3 + 90*a^4*b^4 - 297*a^4*b^3*c - 90*a^4*b^2*c^2 + 543*a^4*b*c^3 + 90*a^4*c^4 + 27*a^3*b^5 + 543*a^3*b^4*c - 390*a^3*b^3*c^2 - 390*a^3*b^2*c^3 - 297*a^3*b*c^4 + 27*a^3*c^5 + 171*a^2*b^5*c - 90*a^2*b^4*c^2 - 390*a^2*b^3*c^3 - 90*a^2*b^2*c^4 - 81*a^2*b*c^5 - 81*a*b^5*c^2 - 297*a*b^4*c^3 + 543*a*b^3*c^4 + 171*a*b^2*c^5 + 27*b^5*c^3 + 90*b^4*c^4 + 27*b^3*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), 1 / a + 1 / b + 1 / c + 5 / (3 * a + b) + 5 / (3 * b + c) + 5 / (3 * c + a) ≥ 9 / (a + 3 * b) + 9 / (b + 3 * c) + 9 / (c + 3 * a)) := @solution
#print axioms solution
