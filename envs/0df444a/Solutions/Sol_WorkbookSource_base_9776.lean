-- Prove2me | solution 1 for WorkbookSource.base_9776
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:46:42.105595+00:00
-- url     : https://prove2.me/submissions/f3612054-f537-4070-a7a0-aade0ea863b6

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (7 * a + b) + 1 / (7 * b + c) + 1 / (7 * c + a)) ≥ (1 / (a + 2 * b + 5 * c) + 1 / (b + 2 * c + 5 * a) + 1 / (c + 2 * a + 5 * b))  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (70*a^5 + 66*a^4*b + 864*a^4*c + 740*a^3*b^2 - 720*a^3*b*c + 2600*a^3*c^2 + 2600*a^2*b^3 - 3620*a^2*b^2*c - 3620*a^2*b*c^2 + 740*a^2*c^3 + 864*a*b^4 - 720*a*b^3*c - 3620*a*b^2*c^2 - 720*a*b*c^3 + 66*a*c^4 + 70*b^5 + 66*b^4*c + 740*b^3*c^2 + 2600*b^2*c^3 + 864*b*c^4 + 70*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (10240 : ℝ) * a^3 * (b - a)^2 + (10240 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (10240 : ℝ) * a^3 * (c - b)^2 + (23680 : ℝ) * a^2 * (b - a)^3 + (40704 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (31104 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (7040 : ℝ) * a^2 * (c - b)^3 + (17920 : ℝ) * a^1 * (b - a)^4 + (42752 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (37888 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (13056 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (1280 : ℝ) * a^1 * (c - b)^4 + (4410 : ℝ) * (b - a)^5 + (13152 : ℝ) * (b - a)^4 * (c - b)^1 + (14424 : ℝ) * (b - a)^3 * (c - b)^2 + (6756 : ℝ) * (b - a)^2 * (c - b)^3 + (1214 : ℝ) * (b - a)^1 * (c - b)^4 + (70 : ℝ) * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (70*a^5 + 66*a^4*b + 864*a^4*c + 740*a^3*b^2 - 720*a^3*b*c + 2600*a^3*c^2 + 2600*a^2*b^3 - 3620*a^2*b^2*c - 3620*a^2*b*c^2 + 740*a^2*c^3 + 864*a*b^4 - 720*a*b^3*c - 3620*a*b^2*c^2 - 720*a*b*c^3 + 66*a*c^4 + 70*b^5 + 66*b^4*c + 740*b^3*c^2 + 2600*b^2*c^3 + 864*b*c^4 + 70*c^5) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (10240 : ℝ) * a^3 * (c - a)^2 + (10240 : ℝ) * a^3 * (c - a)^1 * (b - c)^1 + (10240 : ℝ) * a^3 * (b - c)^2 + (23680 : ℝ) * a^2 * (c - a)^3 + (30336 : ℝ) * a^2 * (c - a)^2 * (b - c)^1 + (20736 : ℝ) * a^2 * (c - a)^1 * (b - c)^2 + (7040 : ℝ) * a^2 * (b - c)^3 + (17920 : ℝ) * a^1 * (c - a)^4 + (28928 : ℝ) * a^1 * (c - a)^3 * (b - c)^1 + (17152 : ℝ) * a^1 * (c - a)^2 * (b - c)^2 + (6144 : ℝ) * a^1 * (c - a)^1 * (b - c)^3 + (1280 : ℝ) * a^1 * (b - c)^4 + (4410 : ℝ) * (c - a)^5 + (8898 : ℝ) * (c - a)^4 * (b - c)^1 + (5916 : ℝ) * (c - a)^3 * (b - c)^2 + (1704 : ℝ) * (c - a)^2 * (b - c)^3 + (416 : ℝ) * (c - a)^1 * (b - c)^4 + (70 : ℝ) * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (70*a^5 + 66*a^4*b + 864*a^4*c + 740*a^3*b^2 - 720*a^3*b*c + 2600*a^3*c^2 + 2600*a^2*b^3 - 3620*a^2*b^2*c - 3620*a^2*b*c^2 + 740*a^2*c^3 + 864*a*b^4 - 720*a*b^3*c - 3620*a*b^2*c^2 - 720*a*b*c^3 + 66*a*c^4 + 70*b^5 + 66*b^4*c + 740*b^3*c^2 + 2600*b^2*c^3 + 864*b*c^4 + 70*c^5) := by
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
  have hn : 0 ≤ (70*a^5 + 66*a^4*b + 864*a^4*c + 740*a^3*b^2 - 720*a^3*b*c + 2600*a^3*c^2 + 2600*a^2*b^3 - 3620*a^2*b^2*c - 3620*a^2*b*c^2 + 740*a^2*c^3 + 864*a*b^4 - 720*a*b^3*c - 3620*a*b^2*c^2 - 720*a*b*c^3 + 66*a*c^4 + 70*b^5 + 66*b^4*c + 740*b^3*c^2 + 2600*b^2*c^3 + 864*b*c^4 + 70*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (1 / (7 * a + b) + 1 / (7 * b + c) + 1 / (7 * c + a)) ≥ (1 / (a + 2 * b + 5 * c) + 1 / (b + 2 * c + 5 * a) + 1 / (c + 2 * a + 5 * b))) := @solution
#print axioms solution
