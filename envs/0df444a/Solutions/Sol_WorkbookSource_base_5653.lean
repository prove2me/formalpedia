-- Prove2me | solution 1 for WorkbookSource.base_5653
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:17:41.622429+00:00
-- url     : https://prove2.me/submissions/ae493e80-4ff4-4596-8f25-a24b698d7c2f

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx: 0 < x) (hy: 0 < y) (hz: 0 < z) : (1 / (101 * x ^ 2 + y * z) + 1 / (101 * y ^ 2 + z * x) + 1 / (101 * z ^ 2 + x * y)) * (x ^ 2 + y ^ 2 + z ^ 2) ≥ 1 / 34 * (x + y + z) ^ 2 / (y * z + z * x + x * y)  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (3434*x^6*y^2 + 6767*x^6*y*z + 3434*x^6*z^2 + 336633*x^5*y^3 + 350100*x^5*y^2*z + 350100*x^5*y*z^2 + 336633*x^5*z^3 - 13534*x^4*y^4 + 336667*x^4*y^3*z - 1023534*x^4*y^2*z^2 + 336667*x^4*y*z^3 - 13534*x^4*z^4 + 336633*x^3*y^5 + 336667*x^3*y^4*z - 1023367*x^3*y^3*z^2 - 1023367*x^3*y^2*z^3 + 336667*x^3*y*z^4 + 336633*x^3*z^5 + 3434*x^2*y^6 + 350100*x^2*y^5*z - 1023534*x^2*y^4*z^2 - 1023367*x^2*y^3*z^3 - 1023534*x^2*y^2*z^4 + 350100*x^2*y*z^5 + 3434*x^2*z^6 + 6767*x*y^6*z + 350100*x*y^5*z^2 + 336667*x*y^4*z^3 + 336667*x*y^3*z^4 + 350100*x*y^2*z^5 + 6767*x*y*z^6 + 3434*y^6*z^2 + 336633*y^5*z^3 - 13534*y^4*z^4 + 336633*y^3*z^5 + 3434*y^2*z^6) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (7211808 : ℝ) * x^6 * (y - x)^2 + (7211808 : ℝ) * x^6 * (y - x)^1 * (z - y)^1 + (7211808 : ℝ) * x^6 * (z - y)^2 + (31472694 : ℝ) * x^5 * (y - x)^3 + (47209041 : ℝ) * x^5 * (y - x)^2 * (z - y)^1 + (39332655 : ℝ) * x^5 * (y - x)^1 * (z - y)^2 + (11798154 : ℝ) * x^5 * (z - y)^3 + (55880937 : ℝ) * x^4 * (y - x)^4 + (111761874 : ℝ) * x^4 * (y - x)^3 * (z - y)^1 + (98765496 : ℝ) * x^4 * (y - x)^2 * (z - y)^2 + (42884559 : ℝ) * x^4 * (y - x)^1 * (z - y)^3 + (6694587 : ℝ) * x^4 * (z - y)^4 + (51577692 : ℝ) * x^3 * (y - x)^5 + (128944230 : ℝ) * x^3 * (y - x)^4 * (z - y)^1 + (131389008 : ℝ) * x^3 * (y - x)^3 * (z - y)^2 + (68139282 : ℝ) * x^3 * (y - x)^2 * (z - y)^3 + (17027364 : ℝ) * x^3 * (y - x)^1 * (z - y)^4 + (1455276 : ℝ) * x^3 * (z - y)^5 + (26010909 : ℝ) * x^2 * (y - x)^6 + (78032727 : ℝ) * x^2 * (y - x)^5 * (z - y)^1 + (93480246 : ℝ) * x^2 * (y - x)^4 * (z - y)^2 + (56905947 : ℝ) * x^2 * (y - x)^3 * (z - y)^3 + (17671338 : ℝ) * x^2 * (y - x)^2 * (z - y)^4 + (2223819 : ℝ) * x^2 * (y - x)^1 * (z - y)^5 + (13635 : ℝ) * x^2 * (z - y)^6 + (6719868 : ℝ) * x^1 * (y - x)^7 + (23519538 : ℝ) * x^1 * (y - x)^6 * (z - y)^1 + (33082422 : ℝ) * x^1 * (y - x)^5 * (z - y)^2 + (23907210 : ℝ) * x^1 * (y - x)^4 * (z - y)^3 + (9073236 : ℝ) * x^1 * (y - x)^3 * (z - y)^4 + (1462413 : ℝ) * x^1 * (y - x)^2 * (z - y)^5 + (13635 : ℝ) * x^1 * (y - x)^1 * (z - y)^6 + (666600 : ℝ) * (y - x)^8 + (2666400 : ℝ) * (y - x)^7 * (z - y)^1 + (4349969 : ℝ) * (y - x)^6 * (z - y)^2 + (3717507 : ℝ) * (y - x)^5 * (z - y)^3 + (1721141 : ℝ) * (y - x)^4 * (z - y)^4 + (357237 : ℝ) * (y - x)^3 * (z - y)^5 + (3434 : ℝ) * (y - x)^2 * (z - y)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (3434*x^6*y^2 + 6767*x^6*y*z + 3434*x^6*z^2 + 336633*x^5*y^3 + 350100*x^5*y^2*z + 350100*x^5*y*z^2 + 336633*x^5*z^3 - 13534*x^4*y^4 + 336667*x^4*y^3*z - 1023534*x^4*y^2*z^2 + 336667*x^4*y*z^3 - 13534*x^4*z^4 + 336633*x^3*y^5 + 336667*x^3*y^4*z - 1023367*x^3*y^3*z^2 - 1023367*x^3*y^2*z^3 + 336667*x^3*y*z^4 + 336633*x^3*z^5 + 3434*x^2*y^6 + 350100*x^2*y^5*z - 1023534*x^2*y^4*z^2 - 1023367*x^2*y^3*z^3 - 1023534*x^2*y^2*z^4 + 350100*x^2*y*z^5 + 3434*x^2*z^6 + 6767*x*y^6*z + 350100*x*y^5*z^2 + 336667*x*y^4*z^3 + 336667*x*y^3*z^4 + 350100*x*y^2*z^5 + 6767*x*y*z^6 + 3434*y^6*z^2 + 336633*y^5*z^3 - 13534*y^4*z^4 + 336633*y^3*z^5 + 3434*y^2*z^6) := by
    rcases le_total x y with hab | hba
    · rcases le_total y z with hbc | hcb
      ·
        convert haux0 x y z (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total x z with hac | hca
        ·
          convert haux0 x z y (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 z x y (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total x z with hbc | hcb
      ·
        convert haux0 y x z (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total y z with hac | hca
        ·
          convert haux0 y z x (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 z y x (by positivity) (by linarith) (by linarith) using 1 <;> ring
  have hn : 0 ≤ (3434*x^6*y^2 + 6767*x^6*y*z + 3434*x^6*z^2 + 336633*x^5*y^3 + 350100*x^5*y^2*z + 350100*x^5*y*z^2 + 336633*x^5*z^3 - 13534*x^4*y^4 + 336667*x^4*y^3*z - 1023534*x^4*y^2*z^2 + 336667*x^4*y*z^3 - 13534*x^4*z^4 + 336633*x^3*y^5 + 336667*x^3*y^4*z - 1023367*x^3*y^3*z^2 - 1023367*x^3*y^2*z^3 + 336667*x^3*y*z^4 + 336633*x^3*z^5 + 3434*x^2*y^6 + 350100*x^2*y^5*z - 1023534*x^2*y^4*z^2 - 1023367*x^2*y^3*z^3 - 1023534*x^2*y^2*z^4 + 350100*x^2*y*z^5 + 3434*x^2*z^6 + 6767*x*y^6*z + 350100*x*y^5*z^2 + 336667*x*y^4*z^3 + 336667*x*y^3*z^4 + 350100*x*y^2*z^5 + 6767*x*y*z^6 + 3434*y^6*z^2 + 336633*y^5*z^3 - 13534*y^4*z^4 + 336633*y^3*z^5 + 3434*y^2*z^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx: 0 < x) (hy: 0 < y) (hz: 0 < z), (1 / (101 * x ^ 2 + y * z) + 1 / (101 * y ^ 2 + z * x) + 1 / (101 * z ^ 2 + x * y)) * (x ^ 2 + y ^ 2 + z ^ 2) ≥ 1 / 34 * (x + y + z) ^ 2 / (y * z + z * x + x * y)) := @solution
#print axioms solution
