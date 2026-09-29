-- Prove2me | solution 1 for WorkbookSource.plus_50631
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:39:26.885773+00:00
-- url     : https://prove2.me/submissions/af102129-45c5-468a-9b0d-129f07f8954e

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 27 * (z + 2 * x + y) ^ 6 ≥ 1024 * (z + x) * (x + y) * (y + z + x) ^ 3 * x   := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (704*x^6 + 1088*x^5*y + 1088*x^5*z + 336*x^4*y^2 - 352*x^4*y*z + 336*x^4*z^2 + 224*x^3*y^3 - 2400*x^3*y^2*z - 2400*x^3*y*z^2 + 224*x^3*z^3 + 596*x^2*y^4 - 688*x^2*y^3*z - 2568*x^2*y^2*z^2 - 688*x^2*y*z^3 + 596*x^2*z^4 + 324*x*y^5 + 596*x*y^4*z + 168*x*y^3*z^2 + 168*x*y^2*z^3 + 596*x*y*z^4 + 324*x*z^5 + 27*y^6 + 162*y^5*z + 405*y^4*z^2 + 540*y^3*z^3 + 405*y^2*z^4 + 162*y*z^5 + 27*z^6) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (18432 : ℝ) * x^4 * (y - x)^2 + (18432 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (11520 : ℝ) * x^4 * (z - y)^2 + (40960 : ℝ) * x^3 * (y - x)^3 + (61440 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (44544 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (12032 : ℝ) * x^3 * (z - y)^3 + (34048 : ℝ) * x^2 * (y - x)^4 + (68096 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (60288 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (26240 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (4432 : ℝ) * x^2 * (z - y)^4 + (12544 : ℝ) * x^1 * (y - x)^5 + (31360 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (33408 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (18752 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (5456 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (648 : ℝ) * x^1 * (z - y)^5 + (1728 : ℝ) * (y - x)^6 + (5184 : ℝ) * (y - x)^5 * (z - y)^1 + (6480 : ℝ) * (y - x)^4 * (z - y)^2 + (4320 : ℝ) * (y - x)^3 * (z - y)^3 + (1620 : ℝ) * (y - x)^2 * (z - y)^4 + (324 : ℝ) * (y - x)^1 * (z - y)^5 + (27 : ℝ) * (z - y)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (x y z : ℝ) (hlow : 0 ≤ y) (hord1 : y ≤ x) (hord2 : x ≤ z) : 0 ≤ (704*x^6 + 1088*x^5*y + 1088*x^5*z + 336*x^4*y^2 - 352*x^4*y*z + 336*x^4*z^2 + 224*x^3*y^3 - 2400*x^3*y^2*z - 2400*x^3*y*z^2 + 224*x^3*z^3 + 596*x^2*y^4 - 688*x^2*y^3*z - 2568*x^2*y^2*z^2 - 688*x^2*y*z^3 + 596*x^2*z^4 + 324*x*y^5 + 596*x*y^4*z + 168*x*y^3*z^2 + 168*x*y^2*z^3 + 596*x*y*z^4 + 324*x*z^5 + 27*y^6 + 162*y^5*z + 405*y^4*z^2 + 540*y^3*z^3 + 405*y^2*z^4 + 162*y*z^5 + 27*z^6) := by
    have hdiff1 : 0 ≤ (x - y) := by linarith
    have hdiff2 : 0 ≤ (z - x) := by linarith
    have hpos : 0 ≤ (11520 : ℝ) * y^4 * (x - y)^2 + (4608 : ℝ) * y^4 * (x - y)^1 * (z - x)^1 + (11520 : ℝ) * y^4 * (z - x)^2 + (34048 : ℝ) * y^3 * (x - y)^3 + (26880 : ℝ) * y^3 * (x - y)^2 * (z - x)^1 + (37632 : ℝ) * y^3 * (x - y)^1 * (z - x)^2 + (12032 : ℝ) * y^3 * (z - x)^3 + (37456 : ℝ) * y^2 * (x - y)^4 + (44480 : ℝ) * y^2 * (x - y)^3 * (z - x)^1 + (51936 : ℝ) * y^2 * (x - y)^2 * (z - x)^2 + (27584 : ℝ) * y^2 * (x - y)^1 * (z - x)^3 + (4432 : ℝ) * y^2 * (z - x)^4 + (18200 : ℝ) * y^1 * (x - y)^5 + (28968 : ℝ) * y^1 * (x - y)^4 * (z - x)^1 + (33648 : ℝ) * y^1 * (x - y)^3 * (z - x)^2 + (22480 : ℝ) * y^1 * (x - y)^2 * (z - x)^3 + (6648 : ℝ) * y^1 * (x - y)^1 * (z - x)^4 + (648 : ℝ) * y^1 * (z - x)^5 + (3299 : ℝ) * (x - y)^6 + (6598 : ℝ) * (x - y)^5 * (z - x)^1 + (8229 : ℝ) * (x - y)^4 * (z - x)^2 + (6388 : ℝ) * (x - y)^3 * (z - x)^3 + (2621 : ℝ) * (x - y)^2 * (z - x)^4 + (486 : ℝ) * (x - y)^1 * (z - x)^5 + (27 : ℝ) * (z - x)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux2 (x y z : ℝ) (hlow : 0 ≤ y) (hord1 : y ≤ z) (hord2 : z ≤ x) : 0 ≤ (704*x^6 + 1088*x^5*y + 1088*x^5*z + 336*x^4*y^2 - 352*x^4*y*z + 336*x^4*z^2 + 224*x^3*y^3 - 2400*x^3*y^2*z - 2400*x^3*y*z^2 + 224*x^3*z^3 + 596*x^2*y^4 - 688*x^2*y^3*z - 2568*x^2*y^2*z^2 - 688*x^2*y*z^3 + 596*x^2*z^4 + 324*x*y^5 + 596*x*y^4*z + 168*x*y^3*z^2 + 168*x*y^2*z^3 + 596*x*y*z^4 + 324*x*z^5 + 27*y^6 + 162*y^5*z + 405*y^4*z^2 + 540*y^3*z^3 + 405*y^2*z^4 + 162*y*z^5 + 27*z^6) := by
    have hdiff1 : 0 ≤ (z - y) := by linarith
    have hdiff2 : 0 ≤ (x - z) := by linarith
    have hpos : 0 ≤ (11520 : ℝ) * y^4 * (z - y)^2 + (18432 : ℝ) * y^4 * (z - y)^1 * (x - z)^1 + (18432 : ℝ) * y^4 * (x - z)^2 + (34048 : ℝ) * y^3 * (z - y)^3 + (75264 : ℝ) * y^3 * (z - y)^2 * (x - z)^1 + (86016 : ℝ) * y^3 * (z - y)^1 * (x - z)^2 + (32768 : ℝ) * y^3 * (x - z)^3 + (37456 : ℝ) * y^2 * (z - y)^4 + (105344 : ℝ) * y^2 * (z - y)^3 * (x - z)^1 + (143232 : ℝ) * y^2 * (z - y)^2 * (x - z)^2 + (92672 : ℝ) * y^2 * (z - y)^1 * (x - z)^3 + (21760 : ℝ) * y^2 * (x - z)^4 + (18200 : ℝ) * y^1 * (z - y)^5 + (62032 : ℝ) * y^1 * (z - y)^4 * (x - z)^1 + (99776 : ℝ) * y^1 * (z - y)^3 * (x - z)^2 + (86656 : ℝ) * y^1 * (z - y)^2 * (x - z)^3 + (37760 : ℝ) * y^1 * (z - y)^1 * (x - z)^4 + (6400 : ℝ) * y^1 * (x - z)^5 + (3299 : ℝ) * (z - y)^6 + (13196 : ℝ) * (z - y)^5 * (x - z)^1 + (24724 : ℝ) * (z - y)^4 * (x - z)^2 + (26528 : ℝ) * (z - y)^3 * (x - z)^3 + (16336 : ℝ) * (z - y)^2 * (x - z)^4 + (5312 : ℝ) * (z - y)^1 * (x - z)^5 + (704 : ℝ) * (x - z)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (704*x^6 + 1088*x^5*y + 1088*x^5*z + 336*x^4*y^2 - 352*x^4*y*z + 336*x^4*z^2 + 224*x^3*y^3 - 2400*x^3*y^2*z - 2400*x^3*y*z^2 + 224*x^3*z^3 + 596*x^2*y^4 - 688*x^2*y^3*z - 2568*x^2*y^2*z^2 - 688*x^2*y*z^3 + 596*x^2*z^4 + 324*x*y^5 + 596*x*y^4*z + 168*x*y^3*z^2 + 168*x*y^2*z^3 + 596*x*y*z^4 + 324*x*z^5 + 27*y^6 + 162*y^5*z + 405*y^4*z^2 + 540*y^3*z^3 + 405*y^2*z^4 + 162*y*z^5 + 27*z^6) := by
    rcases le_total x y with hab | hba
    · rcases le_total y z with hbc | hcb
      ·
        convert haux0 x y z (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total x z with hac | hca
        ·
          convert haux0 x z y (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux1 x z y (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total x z with hbc | hcb
      ·
        convert haux1 x y z (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total y z with hac | hca
        ·
          convert haux2 x y z (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux2 x z y (by positivity) (by linarith) (by linarith) using 1 <;> ring
  nlinarith only [hp]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), 27 * (z + 2 * x + y) ^ 6 ≥ 1024 * (z + x) * (x + y) * (y + z + x) ^ 3 * x) := @solution
#print axioms solution
