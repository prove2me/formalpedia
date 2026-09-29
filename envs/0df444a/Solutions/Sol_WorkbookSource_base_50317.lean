-- Prove2me | solution 1 for WorkbookSource.base_50317
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:44:59.033573+00:00
-- url     : https://prove2.me/submissions/6b01f19c-968f-4d24-8ee2-6169a23a828c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + 2 * b) / (a + b) + (b + 2 * c) / (b + c) + (c + 2 * a) / (c + a) ≤ (9 / 2) * ((a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + c * a)) ^ 2  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (9*a^6*b + 9*a^6*c + 9*a^5*b^2 + 18*a^5*b*c + 9*a^5*c^2 + 10*a^4*b^3 + a^4*b^2*c - a^4*b*c^2 + 8*a^4*c^3 + 8*a^3*b^4 - 18*a^3*b^3*c - 54*a^3*b^2*c^2 - 18*a^3*b*c^3 + 10*a^3*c^4 + 9*a^2*b^5 - a^2*b^4*c - 54*a^2*b^3*c^2 - 54*a^2*b^2*c^3 + a^2*b*c^4 + 9*a^2*c^5 + 9*a*b^6 + 18*a*b^5*c + a*b^4*c^2 - 18*a*b^3*c^3 - a*b^2*c^4 + 18*a*b*c^5 + 9*a*c^6 + 9*b^6*c + 9*b^5*c^2 + 10*b^4*c^3 + 8*b^3*c^4 + 9*b^2*c^5 + 9*b*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (432 : ℝ) * a^5 * (b - a)^2 + (432 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (432 : ℝ) * a^5 * (c - b)^2 + (1440 : ℝ) * a^4 * (b - a)^3 + (2151 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (2151 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (720 : ℝ) * a^4 * (c - b)^3 + (1908 : ℝ) * a^3 * (b - a)^4 + (3792 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (4248 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (2364 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (468 : ℝ) * a^3 * (c - b)^4 + (1260 : ℝ) * a^2 * (b - a)^5 + (3128 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (4024 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (2926 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (1058 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (144 : ℝ) * a^2 * (c - b)^5 + (414 : ℝ) * a^1 * (b - a)^6 + (1234 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (1816 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (1586 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (788 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (198 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (18 : ℝ) * a^1 * (c - b)^6 + (54 : ℝ) * (b - a)^7 + (188 : ℝ) * (b - a)^6 * (c - b)^1 + (312 : ℝ) * (b - a)^5 * (c - b)^2 + (312 : ℝ) * (b - a)^4 * (c - b)^3 + (188 : ℝ) * (b - a)^3 * (c - b)^4 + (63 : ℝ) * (b - a)^2 * (c - b)^5 + (9 : ℝ) * (b - a)^1 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (9*a^6*b + 9*a^6*c + 9*a^5*b^2 + 18*a^5*b*c + 9*a^5*c^2 + 10*a^4*b^3 + a^4*b^2*c - a^4*b*c^2 + 8*a^4*c^3 + 8*a^3*b^4 - 18*a^3*b^3*c - 54*a^3*b^2*c^2 - 18*a^3*b*c^3 + 10*a^3*c^4 + 9*a^2*b^5 - a^2*b^4*c - 54*a^2*b^3*c^2 - 54*a^2*b^2*c^3 + a^2*b*c^4 + 9*a^2*c^5 + 9*a*b^6 + 18*a*b^5*c + a*b^4*c^2 - 18*a*b^3*c^3 - a*b^2*c^4 + 18*a*b*c^5 + 9*a*c^6 + 9*b^6*c + 9*b^5*c^2 + 10*b^4*c^3 + 8*b^3*c^4 + 9*b^2*c^5 + 9*b*c^6) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (432 : ℝ) * a^5 * (c - a)^2 + (432 : ℝ) * a^5 * (c - a)^1 * (b - c)^1 + (432 : ℝ) * a^5 * (b - c)^2 + (1440 : ℝ) * a^4 * (c - a)^3 + (2169 : ℝ) * a^4 * (c - a)^2 * (b - c)^1 + (2169 : ℝ) * a^4 * (c - a)^1 * (b - c)^2 + (720 : ℝ) * a^4 * (b - c)^3 + (1908 : ℝ) * a^3 * (c - a)^4 + (3840 : ℝ) * a^3 * (c - a)^3 * (b - c)^1 + (4320 : ℝ) * a^3 * (c - a)^2 * (b - c)^2 + (2388 : ℝ) * a^3 * (c - a)^1 * (b - c)^3 + (468 : ℝ) * a^3 * (b - c)^4 + (1260 : ℝ) * a^2 * (c - a)^5 + (3172 : ℝ) * a^2 * (c - a)^4 * (b - c)^1 + (4112 : ℝ) * a^2 * (c - a)^3 * (b - c)^2 + (2978 : ℝ) * a^2 * (c - a)^2 * (b - c)^3 + (1066 : ℝ) * a^2 * (c - a)^1 * (b - c)^4 + (144 : ℝ) * a^2 * (b - c)^5 + (414 : ℝ) * a^1 * (c - a)^6 + (1250 : ℝ) * a^1 * (c - a)^5 * (b - c)^1 + (1856 : ℝ) * a^1 * (c - a)^4 * (b - c)^2 + (1618 : ℝ) * a^1 * (c - a)^3 * (b - c)^3 + (796 : ℝ) * a^1 * (c - a)^2 * (b - c)^4 + (198 : ℝ) * a^1 * (c - a)^1 * (b - c)^5 + (18 : ℝ) * a^1 * (b - c)^6 + (54 : ℝ) * (c - a)^7 + (190 : ℝ) * (c - a)^6 * (b - c)^1 + (318 : ℝ) * (c - a)^5 * (b - c)^2 + (318 : ℝ) * (c - a)^4 * (b - c)^3 + (190 : ℝ) * (c - a)^3 * (b - c)^4 + (63 : ℝ) * (c - a)^2 * (b - c)^5 + (9 : ℝ) * (c - a)^1 * (b - c)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (9*a^6*b + 9*a^6*c + 9*a^5*b^2 + 18*a^5*b*c + 9*a^5*c^2 + 10*a^4*b^3 + a^4*b^2*c - a^4*b*c^2 + 8*a^4*c^3 + 8*a^3*b^4 - 18*a^3*b^3*c - 54*a^3*b^2*c^2 - 18*a^3*b*c^3 + 10*a^3*c^4 + 9*a^2*b^5 - a^2*b^4*c - 54*a^2*b^3*c^2 - 54*a^2*b^2*c^3 + a^2*b*c^4 + 9*a^2*c^5 + 9*a*b^6 + 18*a*b^5*c + a*b^4*c^2 - 18*a*b^3*c^3 - a*b^2*c^4 + 18*a*b*c^5 + 9*a*c^6 + 9*b^6*c + 9*b^5*c^2 + 10*b^4*c^3 + 8*b^3*c^4 + 9*b^2*c^5 + 9*b*c^6) := by
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
  have hn : 0 ≤ (9*a^6*b + 9*a^6*c + 9*a^5*b^2 + 18*a^5*b*c + 9*a^5*c^2 + 10*a^4*b^3 + a^4*b^2*c - a^4*b*c^2 + 8*a^4*c^3 + 8*a^3*b^4 - 18*a^3*b^3*c - 54*a^3*b^2*c^2 - 18*a^3*b*c^3 + 10*a^3*c^4 + 9*a^2*b^5 - a^2*b^4*c - 54*a^2*b^3*c^2 - 54*a^2*b^2*c^3 + a^2*b*c^4 + 9*a^2*c^5 + 9*a*b^6 + 18*a*b^5*c + a*b^4*c^2 - 18*a*b^3*c^3 - a*b^2*c^4 + 18*a*b*c^5 + 9*a*c^6 + 9*b^6*c + 9*b^5*c^2 + 10*b^4*c^3 + 8*b^3*c^4 + 9*b^2*c^5 + 9*b*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a + 2 * b) / (a + b) + (b + 2 * c) / (b + c) + (c + 2 * a) / (c + a) ≤ (9 / 2) * ((a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + c * a)) ^ 2) := @solution
#print axioms solution
