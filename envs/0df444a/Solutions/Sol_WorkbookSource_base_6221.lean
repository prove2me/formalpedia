-- Prove2me | solution 1 for WorkbookSource.base_6221
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:19:08.237576+00:00
-- url     : https://prove2.me/submissions/3f2f0216-ed31-4ef2-b29b-5feddc892cb1

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (5 * a ^ 2 + 2 * b * c + 5 * b ^ 2) + b / (5 * b ^ 2 + 2 * c * a + 5 * c ^ 2) + c / (5 * c ^ 2 + 2 * a * b + 5 * a ^ 2)) ≤ (a * b + b * c + c * a) / (12 * a * b * c)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (50*a^6*b*c + 50*a^6*c^2 + 125*a^5*b^3 - 155*a^5*b^2*c + 75*a^5*b*c^2 + 125*a^5*c^3 + 50*a^4*b^4 - 195*a^4*b^3*c + 92*a^4*b^2*c^2 - 175*a^4*b*c^3 + 50*a^4*c^4 + 125*a^3*b^5 - 175*a^3*b^4*c - 42*a^3*b^3*c^2 - 42*a^3*b^2*c^3 - 195*a^3*b*c^4 + 125*a^3*c^5 + 50*a^2*b^6 + 75*a^2*b^5*c + 92*a^2*b^4*c^2 - 42*a^2*b^3*c^3 + 92*a^2*b^2*c^4 - 155*a^2*b*c^5 + 50*a*b^6*c - 155*a*b^5*c^2 - 195*a*b^4*c^3 - 175*a*b^3*c^4 + 75*a*b^2*c^5 + 50*a*b*c^6 + 125*b^5*c^3 + 50*b^4*c^4 + 125*b^3*c^5 + 50*b^2*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (1632 : ℝ) * a^6 * (b - a)^2 + (1632 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (1632 : ℝ) * a^6 * (c - b)^2 + (7008 : ℝ) * a^5 * (b - a)^3 + (11832 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (10392 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (2784 : ℝ) * a^5 * (c - b)^3 + (12732 : ℝ) * a^4 * (b - a)^4 + (29864 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (30636 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (13504 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (2172 : ℝ) * a^4 * (c - b)^4 + (12718 : ℝ) * a^3 * (b - a)^5 + (37540 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (46384 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (27636 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (7614 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (770 : ℝ) * a^3 * (c - b)^5 + (7462 : ℝ) * a^2 * (b - a)^6 + (26006 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (37643 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (27946 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (10717 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (1870 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (100 : ℝ) * a^2 * (c - b)^6 + (2450 : ℝ) * a^1 * (b - a)^7 + (9630 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (15760 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (13730 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (6650 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (1650 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (150 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (350 : ℝ) * (b - a)^8 + (1500 : ℝ) * (b - a)^7 * (c - b)^1 + (2675 : ℝ) * (b - a)^6 * (c - b)^2 + (2575 : ℝ) * (b - a)^5 * (c - b)^3 + (1425 : ℝ) * (b - a)^4 * (c - b)^4 + (425 : ℝ) * (b - a)^3 * (c - b)^5 + (50 : ℝ) * (b - a)^2 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (50*a^6*b*c + 50*a^6*c^2 + 125*a^5*b^3 - 155*a^5*b^2*c + 75*a^5*b*c^2 + 125*a^5*c^3 + 50*a^4*b^4 - 195*a^4*b^3*c + 92*a^4*b^2*c^2 - 175*a^4*b*c^3 + 50*a^4*c^4 + 125*a^3*b^5 - 175*a^3*b^4*c - 42*a^3*b^3*c^2 - 42*a^3*b^2*c^3 - 195*a^3*b*c^4 + 125*a^3*c^5 + 50*a^2*b^6 + 75*a^2*b^5*c + 92*a^2*b^4*c^2 - 42*a^2*b^3*c^3 + 92*a^2*b^2*c^4 - 155*a^2*b*c^5 + 50*a*b^6*c - 155*a*b^5*c^2 - 195*a*b^4*c^3 - 175*a*b^3*c^4 + 75*a*b^2*c^5 + 50*a*b*c^6 + 125*b^5*c^3 + 50*b^4*c^4 + 125*b^3*c^5 + 50*b^2*c^6) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (1632 : ℝ) * a^6 * (c - a)^2 + (1632 : ℝ) * a^6 * (c - a)^1 * (b - c)^1 + (1632 : ℝ) * a^6 * (b - c)^2 + (7008 : ℝ) * a^5 * (c - a)^3 + (9192 : ℝ) * a^5 * (c - a)^2 * (b - c)^1 + (7752 : ℝ) * a^5 * (c - a)^1 * (b - c)^2 + (2784 : ℝ) * a^5 * (b - c)^3 + (12732 : ℝ) * a^4 * (c - a)^4 + (21064 : ℝ) * a^4 * (c - a)^3 * (b - c)^1 + (17436 : ℝ) * a^4 * (c - a)^2 * (b - c)^2 + (9104 : ℝ) * a^4 * (c - a)^1 * (b - c)^3 + (2172 : ℝ) * a^4 * (b - c)^4 + (12718 : ℝ) * a^3 * (c - a)^5 + (26050 : ℝ) * a^3 * (c - a)^4 * (b - c)^1 + (23404 : ℝ) * a^3 * (c - a)^3 * (b - c)^2 + (13456 : ℝ) * a^3 * (c - a)^2 * (b - c)^3 + (4924 : ℝ) * a^3 * (c - a)^1 * (b - c)^4 + (770 : ℝ) * a^3 * (b - c)^5 + (7462 : ℝ) * a^2 * (c - a)^6 + (18766 : ℝ) * a^2 * (c - a)^5 * (b - c)^1 + (19543 : ℝ) * a^2 * (c - a)^4 * (b - c)^2 + (11806 : ℝ) * a^2 * (c - a)^3 * (b - c)^3 + (4607 : ℝ) * a^2 * (c - a)^2 * (b - c)^4 + (1040 : ℝ) * a^2 * (c - a)^1 * (b - c)^5 + (100 : ℝ) * a^2 * (b - c)^6 + (2450 : ℝ) * a^1 * (c - a)^7 + (7520 : ℝ) * a^1 * (c - a)^6 * (b - c)^1 + (9430 : ℝ) * a^1 * (c - a)^5 * (b - c)^2 + (6370 : ℝ) * a^1 * (c - a)^4 * (b - c)^3 + (2480 : ℝ) * a^1 * (c - a)^3 * (b - c)^4 + (520 : ℝ) * a^1 * (c - a)^2 * (b - c)^5 + (50 : ℝ) * a^1 * (c - a)^1 * (b - c)^6 + (350 : ℝ) * (c - a)^8 + (1300 : ℝ) * (c - a)^7 * (b - c)^1 + (1975 : ℝ) * (c - a)^6 * (b - c)^2 + (1575 : ℝ) * (c - a)^5 * (b - c)^3 + (675 : ℝ) * (c - a)^4 * (b - c)^4 + (125 : ℝ) * (c - a)^3 * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (50*a^6*b*c + 50*a^6*c^2 + 125*a^5*b^3 - 155*a^5*b^2*c + 75*a^5*b*c^2 + 125*a^5*c^3 + 50*a^4*b^4 - 195*a^4*b^3*c + 92*a^4*b^2*c^2 - 175*a^4*b*c^3 + 50*a^4*c^4 + 125*a^3*b^5 - 175*a^3*b^4*c - 42*a^3*b^3*c^2 - 42*a^3*b^2*c^3 - 195*a^3*b*c^4 + 125*a^3*c^5 + 50*a^2*b^6 + 75*a^2*b^5*c + 92*a^2*b^4*c^2 - 42*a^2*b^3*c^3 + 92*a^2*b^2*c^4 - 155*a^2*b*c^5 + 50*a*b^6*c - 155*a*b^5*c^2 - 195*a*b^4*c^3 - 175*a*b^3*c^4 + 75*a*b^2*c^5 + 50*a*b*c^6 + 125*b^5*c^3 + 50*b^4*c^4 + 125*b^3*c^5 + 50*b^2*c^6) := by
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
  have hn : 0 ≤ (50*a^6*b*c + 50*a^6*c^2 + 125*a^5*b^3 - 155*a^5*b^2*c + 75*a^5*b*c^2 + 125*a^5*c^3 + 50*a^4*b^4 - 195*a^4*b^3*c + 92*a^4*b^2*c^2 - 175*a^4*b*c^3 + 50*a^4*c^4 + 125*a^3*b^5 - 175*a^3*b^4*c - 42*a^3*b^3*c^2 - 42*a^3*b^2*c^3 - 195*a^3*b*c^4 + 125*a^3*c^5 + 50*a^2*b^6 + 75*a^2*b^5*c + 92*a^2*b^4*c^2 - 42*a^2*b^3*c^3 + 92*a^2*b^2*c^4 - 155*a^2*b*c^5 + 50*a*b^6*c - 155*a*b^5*c^2 - 195*a*b^4*c^3 - 175*a*b^3*c^4 + 75*a*b^2*c^5 + 50*a*b*c^6 + 125*b^5*c^3 + 50*b^4*c^4 + 125*b^3*c^5 + 50*b^2*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a / (5 * a ^ 2 + 2 * b * c + 5 * b ^ 2) + b / (5 * b ^ 2 + 2 * c * a + 5 * c ^ 2) + c / (5 * c ^ 2 + 2 * a * b + 5 * a ^ 2)) ≤ (a * b + b * c + c * a) / (12 * a * b * c)) := @solution
#print axioms solution
