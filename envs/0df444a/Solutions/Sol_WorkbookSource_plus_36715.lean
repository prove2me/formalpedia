-- Prove2me | solution 1 for WorkbookSource.plus_36715
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:58:32.294689+00:00
-- url     : https://prove2.me/submissions/840530ab-846a-4085-8f28-9724bd40ff07

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (4 * a + b - c) ^ 2 / (2 * a ^ 2 + (b + c) ^ 2) + (4 * b + c - a) ^ 2 / (2 * b ^ 2 + (c + a) ^ 2) + (4 * c + a - b) ^ 2 / (2 * c ^ 2 + (a + b) ^ 2) ≥ 8   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^6 - 8*a^5*b + 8*a^5*c + 19*a^4*b^2 - 30*a^4*b*c + 51*a^4*c^2 + 42*a^3*b^3 + 14*a^3*b^2*c - 114*a^3*b*c^2 + 42*a^3*c^3 + 51*a^2*b^4 - 114*a^2*b^3*c + 42*a^2*b^2*c^2 + 14*a^2*b*c^3 + 19*a^2*c^4 + 8*a*b^5 - 30*a*b^4*c + 14*a*b^3*c^2 - 114*a*b^2*c^3 - 30*a*b*c^4 - 8*a*c^5 + 4*b^6 - 8*b^5*c + 19*b^4*c^2 + 42*b^3*c^3 + 51*b^2*c^4 + 8*b*c^5 + 4*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (264 : ℝ) * a^4 * (b - a)^2 + (264 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (264 : ℝ) * a^4 * (c - b)^2 + (832 : ℝ) * a^3 * (b - a)^3 + (1392 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (1008 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (224 : ℝ) * a^3 * (c - b)^3 + (1012 : ℝ) * a^2 * (b - a)^4 + (2312 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (1980 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (680 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (100 : ℝ) * a^2 * (c - b)^4 + (560 : ℝ) * a^1 * (b - a)^5 + (1616 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (1776 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (904 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (232 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (24 : ℝ) * a^1 * (c - b)^5 + (120 : ℝ) * (b - a)^6 + (424 : ℝ) * (b - a)^5 * (c - b)^1 + (591 : ℝ) * (b - a)^4 * (c - b)^2 + (406 : ℝ) * (b - a)^3 * (c - b)^3 + (151 : ℝ) * (b - a)^2 * (c - b)^4 + (32 : ℝ) * (b - a)^1 * (c - b)^5 + (4 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (4*a^6 - 8*a^5*b + 8*a^5*c + 19*a^4*b^2 - 30*a^4*b*c + 51*a^4*c^2 + 42*a^3*b^3 + 14*a^3*b^2*c - 114*a^3*b*c^2 + 42*a^3*c^3 + 51*a^2*b^4 - 114*a^2*b^3*c + 42*a^2*b^2*c^2 + 14*a^2*b*c^3 + 19*a^2*c^4 + 8*a*b^5 - 30*a*b^4*c + 14*a*b^3*c^2 - 114*a*b^2*c^3 - 30*a*b*c^4 - 8*a*c^5 + 4*b^6 - 8*b^5*c + 19*b^4*c^2 + 42*b^3*c^3 + 51*b^2*c^4 + 8*b*c^5 + 4*c^6) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (264 : ℝ) * a^4 * (c - a)^2 + (264 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (264 : ℝ) * a^4 * (b - c)^2 + (832 : ℝ) * a^3 * (c - a)^3 + (1104 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (720 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (224 : ℝ) * a^3 * (b - c)^3 + (1012 : ℝ) * a^2 * (c - a)^4 + (1736 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (1116 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (392 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (100 : ℝ) * a^2 * (b - c)^4 + (560 : ℝ) * a^1 * (c - a)^5 + (1184 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (912 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (328 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (88 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (24 : ℝ) * a^1 * (b - c)^5 + (120 : ℝ) * (c - a)^6 + (296 : ℝ) * (c - a)^5 * (b - c)^1 + (271 : ℝ) * (c - a)^4 * (b - c)^2 + (118 : ℝ) * (c - a)^3 * (b - c)^3 + (39 : ℝ) * (c - a)^2 * (b - c)^4 + (16 : ℝ) * (c - a)^1 * (b - c)^5 + (4 : ℝ) * (b - c)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^6 - 8*a^5*b + 8*a^5*c + 19*a^4*b^2 - 30*a^4*b*c + 51*a^4*c^2 + 42*a^3*b^3 + 14*a^3*b^2*c - 114*a^3*b*c^2 + 42*a^3*c^3 + 51*a^2*b^4 - 114*a^2*b^3*c + 42*a^2*b^2*c^2 + 14*a^2*b*c^3 + 19*a^2*c^4 + 8*a*b^5 - 30*a*b^4*c + 14*a*b^3*c^2 - 114*a*b^2*c^3 - 30*a*b*c^4 - 8*a*c^5 + 4*b^6 - 8*b^5*c + 19*b^4*c^2 + 42*b^3*c^3 + 51*b^2*c^4 + 8*b*c^5 + 4*c^6) := by
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
  have hn : 0 ≤ (4*a^6 - 8*a^5*b + 8*a^5*c + 19*a^4*b^2 - 30*a^4*b*c + 51*a^4*c^2 + 42*a^3*b^3 + 14*a^3*b^2*c - 114*a^3*b*c^2 + 42*a^3*c^3 + 51*a^2*b^4 - 114*a^2*b^3*c + 42*a^2*b^2*c^2 + 14*a^2*b*c^3 + 19*a^2*c^4 + 8*a*b^5 - 30*a*b^4*c + 14*a*b^3*c^2 - 114*a*b^2*c^3 - 30*a*b*c^4 - 8*a*c^5 + 4*b^6 - 8*b^5*c + 19*b^4*c^2 + 42*b^3*c^3 + 51*b^2*c^4 + 8*b*c^5 + 4*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (4 * a + b - c) ^ 2 / (2 * a ^ 2 + (b + c) ^ 2) + (4 * b + c - a) ^ 2 / (2 * b ^ 2 + (c + a) ^ 2) + (4 * c + a - b) ^ 2 / (2 * c ^ 2 + (a + b) ^ 2) ≥ 8) := @solution
#print axioms solution
