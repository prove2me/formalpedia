-- Prove2me | solution 1 for WorkbookSource.base_52794
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T11:34:15.335131+00:00
-- url     : https://prove2.me/submissions/d8bd2dc6-6c31-461b-945d-6a067c502e34

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
private lemma p2mIndependent0 (gap0 gap1 gap2 gap3 : ℝ) (hg0 : 0 ≤ gap0) (hg1 : 0 ≤ gap1) (hg2 : 0 ≤ gap2) (hg3 : 0 ≤ gap3) : 0 ≤ ((gap0)^3*(gap0 + gap1)^2*(gap0 + gap1 + gap2) + (gap0)^3*(gap0 + gap1)^2*(gap0 + gap1 + gap2 + gap3) + (gap0)^3*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3)^2 + (gap0)^3*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3)^2 + (gap0)^2*(gap0 + gap1)^3*(gap0 + gap1 + gap2) + (gap0)^2*(gap0 + gap1)^3*(gap0 + gap1 + gap2 + gap3) - 2*(gap0)^2*(gap0 + gap1)^2*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3) - 4*(gap0)^2*(gap0 + gap1)*(gap0 + gap1 + gap2)^2*(gap0 + gap1 + gap2 + gap3) - 2*(gap0)^2*(gap0 + gap1)*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3)^2 + (gap0)^2*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3)^3 + (gap0)^2*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3)^3 + (gap0)*(gap0 + gap1)^3*(gap0 + gap1 + gap2)^2 + (gap0)*(gap0 + gap1)^2*(gap0 + gap1 + gap2)^3 - 2*(gap0)*(gap0 + gap1)^2*(gap0 + gap1 + gap2)^2*(gap0 + gap1 + gap2 + gap3) - 4*(gap0)*(gap0 + gap1)^2*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3)^2 - 2*(gap0)*(gap0 + gap1)*(gap0 + gap1 + gap2)^2*(gap0 + gap1 + gap2 + gap3)^2 + (gap0)*(gap0 + gap1 + gap2)^3*(gap0 + gap1 + gap2 + gap3)^2 + (gap0)*(gap0 + gap1 + gap2)^2*(gap0 + gap1 + gap2 + gap3)^3 + (gap0 + gap1)^3*(gap0 + gap1 + gap2)^2*(gap0 + gap1 + gap2 + gap3) + (gap0 + gap1)^2*(gap0 + gap1 + gap2)^3*(gap0 + gap1 + gap2 + gap3) + (gap0 + gap1)*(gap0 + gap1 + gap2)^3*(gap0 + gap1 + gap2 + gap3)^2 + (gap0 + gap1)*(gap0 + gap1 + gap2)^2*(gap0 + gap1 + gap2 + gap3)^3) := by
  have hpos : 0 ≤ (8 : ℝ) * (gap0^4 * gap1^2) + (16 : ℝ) * (gap0^4 * gap1^1 * gap2^1) + (16 : ℝ) * (gap0^4 * gap2^2) + (16 : ℝ) * (gap0^4 * gap2^1 * gap3^1) + (8 : ℝ) * (gap0^4 * gap3^2) + (28 : ℝ) * (gap0^3 * gap1^3) + (72 : ℝ) * (gap0^3 * gap1^2 * gap2^1) + (12 : ℝ) * (gap0^3 * gap1^2 * gap3^1) + (80 : ℝ) * (gap0^3 * gap1^1 * gap2^2) + (64 : ℝ) * (gap0^3 * gap1^1 * gap2^1 * gap3^1) + (20 : ℝ) * (gap0^3 * gap1^1 * gap3^2) + (32 : ℝ) * (gap0^3 * gap2^3) + (48 : ℝ) * (gap0^3 * gap2^2 * gap3^1) + (24 : ℝ) * (gap0^3 * gap2^1 * gap3^2) + (4 : ℝ) * (gap0^3 * gap3^3) + (36 : ℝ) * (gap0^2 * gap1^4) + (113 : ℝ) * (gap0^2 * gap1^3 * gap2^1) + (31 : ℝ) * (gap0^2 * gap1^3 * gap3^1) + (145 : ℝ) * (gap0^2 * gap1^2 * gap2^2) + (111 : ℝ) * (gap0^2 * gap1^2 * gap2^1 * gap3^1) + (22 : ℝ) * (gap0^2 * gap1^2 * gap3^2) + (88 : ℝ) * (gap0^2 * gap1^1 * gap2^3) + (122 : ℝ) * (gap0^2 * gap1^1 * gap2^2 * gap3^1) + (51 : ℝ) * (gap0^2 * gap1^1 * gap2^1 * gap3^2) + (7 : ℝ) * (gap0^2 * gap1^1 * gap3^3) + (20 : ℝ) * (gap0^2 * gap2^4) + (40 : ℝ) * (gap0^2 * gap2^3 * gap3^1) + (25 : ℝ) * (gap0^2 * gap2^2 * gap3^2) + (5 : ℝ) * (gap0^2 * gap2^1 * gap3^3) + (20 : ℝ) * (gap0^1 * gap1^5) + (74 : ℝ) * (gap0^1 * gap1^4 * gap2^1) + (26 : ℝ) * (gap0^1 * gap1^4 * gap3^1) + (110 : ℝ) * (gap0^1 * gap1^3 * gap2^2) + (88 : ℝ) * (gap0^1 * gap1^3 * gap2^1 * gap3^1) + (14 : ℝ) * (gap0^1 * gap1^3 * gap3^2) + (82 : ℝ) * (gap0^1 * gap1^2 * gap2^3) + (110 : ℝ) * (gap0^1 * gap1^2 * gap2^2 * gap3^1) + (40 : ℝ) * (gap0^1 * gap1^2 * gap2^1 * gap3^2) + (4 : ℝ) * (gap0^1 * gap1^2 * gap3^3) + (30 : ℝ) * (gap0^1 * gap1^1 * gap2^4) + (58 : ℝ) * (gap0^1 * gap1^1 * gap2^3 * gap3^1) + (34 : ℝ) * (gap0^1 * gap1^1 * gap2^2 * gap3^2) + (6 : ℝ) * (gap0^1 * gap1^1 * gap2^1 * gap3^3) + (4 : ℝ) * (gap0^1 * gap2^5) + (10 : ℝ) * (gap0^1 * gap2^4 * gap3^1) + (8 : ℝ) * (gap0^1 * gap2^3 * gap3^2) + (2 : ℝ) * (gap0^1 * gap2^2 * gap3^3) + (4 : ℝ) * (gap1^6) + (17 : ℝ) * (gap1^5 * gap2^1) + (7 : ℝ) * (gap1^5 * gap3^1) + (29 : ℝ) * (gap1^4 * gap2^2) + (25 : ℝ) * (gap1^4 * gap2^1 * gap3^1) + (4 : ℝ) * (gap1^4 * gap3^2) + (25 : ℝ) * (gap1^3 * gap2^3) + (34 : ℝ) * (gap1^3 * gap2^2 * gap3^1) + (12 : ℝ) * (gap1^3 * gap2^1 * gap3^2) + (1 : ℝ) * (gap1^3 * gap3^3) + (11 : ℝ) * (gap1^2 * gap2^4) + (21 : ℝ) * (gap1^2 * gap2^3 * gap3^1) + (12 : ℝ) * (gap1^2 * gap2^2 * gap3^2) + (2 : ℝ) * (gap1^2 * gap2^1 * gap3^3) + (2 : ℝ) * (gap1^1 * gap2^5) + (5 : ℝ) * (gap1^1 * gap2^4 * gap3^1) + (4 : ℝ) * (gap1^1 * gap2^3 * gap3^2) + (1 : ℝ) * (gap1^1 * gap2^2 * gap3^3) := by positivity
  convert hpos using 1 <;> ring

private lemma p2mIndependent1 (gap0 gap1 gap2 gap3 : ℝ) (hg0 : 0 ≤ gap0) (hg1 : 0 ≤ gap1) (hg2 : 0 ≤ gap2) (hg3 : 0 ≤ gap3) : 0 ≤ ((gap0)^3*(gap0 + gap1)^2*(gap0 + gap1 + gap2 + gap3) + (gap0)^3*(gap0 + gap1)^2*(gap0 + gap1 + gap2) + (gap0)^3*(gap0 + gap1)*(gap0 + gap1 + gap2)^2 + (gap0)^3*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1 + gap2)^2 + (gap0)^2*(gap0 + gap1)^3*(gap0 + gap1 + gap2 + gap3) + (gap0)^2*(gap0 + gap1)^3*(gap0 + gap1 + gap2) - 2*(gap0)^2*(gap0 + gap1)^2*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1 + gap2) - 4*(gap0)^2*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3)^2*(gap0 + gap1 + gap2) - 2*(gap0)^2*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1 + gap2)^2 + (gap0)^2*(gap0 + gap1)*(gap0 + gap1 + gap2)^3 + (gap0)^2*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1 + gap2)^3 + (gap0)*(gap0 + gap1)^3*(gap0 + gap1 + gap2 + gap3)^2 + (gap0)*(gap0 + gap1)^2*(gap0 + gap1 + gap2 + gap3)^3 - 2*(gap0)*(gap0 + gap1)^2*(gap0 + gap1 + gap2 + gap3)^2*(gap0 + gap1 + gap2) - 4*(gap0)*(gap0 + gap1)^2*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1 + gap2)^2 - 2*(gap0)*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3)^2*(gap0 + gap1 + gap2)^2 + (gap0)*(gap0 + gap1 + gap2 + gap3)^3*(gap0 + gap1 + gap2)^2 + (gap0)*(gap0 + gap1 + gap2 + gap3)^2*(gap0 + gap1 + gap2)^3 + (gap0 + gap1)^3*(gap0 + gap1 + gap2 + gap3)^2*(gap0 + gap1 + gap2) + (gap0 + gap1)^2*(gap0 + gap1 + gap2 + gap3)^3*(gap0 + gap1 + gap2) + (gap0 + gap1)*(gap0 + gap1 + gap2 + gap3)^3*(gap0 + gap1 + gap2)^2 + (gap0 + gap1)*(gap0 + gap1 + gap2 + gap3)^2*(gap0 + gap1 + gap2)^3) := by
  have hpos : 0 ≤ (8 : ℝ) * (gap0^4 * gap1^2) + (16 : ℝ) * (gap0^4 * gap1^1 * gap2^1) + (16 : ℝ) * (gap0^4 * gap1^1 * gap3^1) + (16 : ℝ) * (gap0^4 * gap2^2) + (16 : ℝ) * (gap0^4 * gap2^1 * gap3^1) + (8 : ℝ) * (gap0^4 * gap3^2) + (28 : ℝ) * (gap0^3 * gap1^3) + (72 : ℝ) * (gap0^3 * gap1^2 * gap2^1) + (60 : ℝ) * (gap0^3 * gap1^2 * gap3^1) + (80 : ℝ) * (gap0^3 * gap1^1 * gap2^2) + (96 : ℝ) * (gap0^3 * gap1^1 * gap2^1 * gap3^1) + (36 : ℝ) * (gap0^3 * gap1^1 * gap3^2) + (32 : ℝ) * (gap0^3 * gap2^3) + (48 : ℝ) * (gap0^3 * gap2^2 * gap3^1) + (24 : ℝ) * (gap0^3 * gap2^1 * gap3^2) + (4 : ℝ) * (gap0^3 * gap3^3) + (36 : ℝ) * (gap0^2 * gap1^4) + (113 : ℝ) * (gap0^2 * gap1^3 * gap2^1) + (82 : ℝ) * (gap0^2 * gap1^3 * gap3^1) + (145 : ℝ) * (gap0^2 * gap1^2 * gap2^2) + (179 : ℝ) * (gap0^2 * gap1^2 * gap2^1 * gap3^1) + (56 : ℝ) * (gap0^2 * gap1^2 * gap3^2) + (88 : ℝ) * (gap0^2 * gap1^1 * gap2^3) + (142 : ℝ) * (gap0^2 * gap1^1 * gap2^2 * gap3^1) + (71 : ℝ) * (gap0^2 * gap1^1 * gap2^1 * gap3^2) + (10 : ℝ) * (gap0^2 * gap1^1 * gap3^3) + (20 : ℝ) * (gap0^2 * gap2^4) + (40 : ℝ) * (gap0^2 * gap2^3 * gap3^1) + (25 : ℝ) * (gap0^2 * gap2^2 * gap3^2) + (5 : ℝ) * (gap0^2 * gap2^1 * gap3^3) + (20 : ℝ) * (gap0^1 * gap1^5) + (74 : ℝ) * (gap0^1 * gap1^4 * gap2^1) + (48 : ℝ) * (gap0^1 * gap1^4 * gap3^1) + (110 : ℝ) * (gap0^1 * gap1^3 * gap2^2) + (132 : ℝ) * (gap0^1 * gap1^3 * gap2^1 * gap3^1) + (36 : ℝ) * (gap0^1 * gap1^3 * gap3^2) + (82 : ℝ) * (gap0^1 * gap1^2 * gap2^3) + (136 : ℝ) * (gap0^1 * gap1^2 * gap2^2 * gap3^1) + (66 : ℝ) * (gap0^1 * gap1^2 * gap2^1 * gap3^2) + (8 : ℝ) * (gap0^1 * gap1^2 * gap3^3) + (30 : ℝ) * (gap0^1 * gap1^1 * gap2^4) + (62 : ℝ) * (gap0^1 * gap1^1 * gap2^3 * gap3^1) + (40 : ℝ) * (gap0^1 * gap1^1 * gap2^2 * gap3^2) + (8 : ℝ) * (gap0^1 * gap1^1 * gap2^1 * gap3^3) + (4 : ℝ) * (gap0^1 * gap2^5) + (10 : ℝ) * (gap0^1 * gap2^4 * gap3^1) + (8 : ℝ) * (gap0^1 * gap2^3 * gap3^2) + (2 : ℝ) * (gap0^1 * gap2^2 * gap3^3) + (4 : ℝ) * (gap1^6) + (17 : ℝ) * (gap1^5 * gap2^1) + (10 : ℝ) * (gap1^5 * gap3^1) + (29 : ℝ) * (gap1^4 * gap2^2) + (33 : ℝ) * (gap1^4 * gap2^1 * gap3^1) + (8 : ℝ) * (gap1^4 * gap3^2) + (25 : ℝ) * (gap1^3 * gap2^3) + (41 : ℝ) * (gap1^3 * gap2^2 * gap3^1) + (19 : ℝ) * (gap1^3 * gap2^1 * gap3^2) + (2 : ℝ) * (gap1^3 * gap3^3) + (11 : ℝ) * (gap1^2 * gap2^4) + (23 : ℝ) * (gap1^2 * gap2^3 * gap3^1) + (15 : ℝ) * (gap1^2 * gap2^2 * gap3^2) + (3 : ℝ) * (gap1^2 * gap2^1 * gap3^3) + (2 : ℝ) * (gap1^1 * gap2^5) + (5 : ℝ) * (gap1^1 * gap2^4 * gap3^1) + (4 : ℝ) * (gap1^1 * gap2^3 * gap3^2) + (1 : ℝ) * (gap1^1 * gap2^2 * gap3^3) := by positivity
  convert hpos using 1 <;> ring

private lemma p2mIndependent2 (gap0 gap1 gap2 gap3 : ℝ) (hg0 : 0 ≤ gap0) (hg1 : 0 ≤ gap1) (hg2 : 0 ≤ gap2) (hg3 : 0 ≤ gap3) : 0 ≤ ((gap0)^3*(gap0 + gap1 + gap2)^2*(gap0 + gap1) + (gap0)^3*(gap0 + gap1 + gap2)^2*(gap0 + gap1 + gap2 + gap3) + (gap0)^3*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3)^2 + (gap0)^3*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3)^2 + (gap0)^2*(gap0 + gap1 + gap2)^3*(gap0 + gap1) + (gap0)^2*(gap0 + gap1 + gap2)^3*(gap0 + gap1 + gap2 + gap3) - 2*(gap0)^2*(gap0 + gap1 + gap2)^2*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3) - 4*(gap0)^2*(gap0 + gap1 + gap2)*(gap0 + gap1)^2*(gap0 + gap1 + gap2 + gap3) - 2*(gap0)^2*(gap0 + gap1 + gap2)*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3)^2 + (gap0)^2*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3)^3 + (gap0)^2*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3)^3 + (gap0)*(gap0 + gap1 + gap2)^3*(gap0 + gap1)^2 + (gap0)*(gap0 + gap1 + gap2)^2*(gap0 + gap1)^3 - 2*(gap0)*(gap0 + gap1 + gap2)^2*(gap0 + gap1)^2*(gap0 + gap1 + gap2 + gap3) - 4*(gap0)*(gap0 + gap1 + gap2)^2*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3)^2 - 2*(gap0)*(gap0 + gap1 + gap2)*(gap0 + gap1)^2*(gap0 + gap1 + gap2 + gap3)^2 + (gap0)*(gap0 + gap1)^3*(gap0 + gap1 + gap2 + gap3)^2 + (gap0)*(gap0 + gap1)^2*(gap0 + gap1 + gap2 + gap3)^3 + (gap0 + gap1 + gap2)^3*(gap0 + gap1)^2*(gap0 + gap1 + gap2 + gap3) + (gap0 + gap1 + gap2)^2*(gap0 + gap1)^3*(gap0 + gap1 + gap2 + gap3) + (gap0 + gap1 + gap2)*(gap0 + gap1)^3*(gap0 + gap1 + gap2 + gap3)^2 + (gap0 + gap1 + gap2)*(gap0 + gap1)^2*(gap0 + gap1 + gap2 + gap3)^3) := by
  have hpos : 0 ≤ (8 : ℝ) * (gap0^4 * gap1^2) + (8 : ℝ) * (gap0^4 * gap3^2) + (28 : ℝ) * (gap0^3 * gap1^3) + (24 : ℝ) * (gap0^3 * gap1^2 * gap2^1) + (12 : ℝ) * (gap0^3 * gap1^2 * gap3^1) + (20 : ℝ) * (gap0^3 * gap1^1 * gap3^2) + (8 : ℝ) * (gap0^3 * gap2^1 * gap3^2) + (4 : ℝ) * (gap0^3 * gap3^3) + (36 : ℝ) * (gap0^2 * gap1^4) + (62 : ℝ) * (gap0^2 * gap1^3 * gap2^1) + (31 : ℝ) * (gap0^2 * gap1^3 * gap3^1) + (26 : ℝ) * (gap0^2 * gap1^2 * gap2^2) + (26 : ℝ) * (gap0^2 * gap1^2 * gap2^1 * gap3^1) + (22 : ℝ) * (gap0^2 * gap1^2 * gap3^2) + (14 : ℝ) * (gap0^2 * gap1^1 * gap2^1 * gap3^2) + (7 : ℝ) * (gap0^2 * gap1^1 * gap3^3) + (2 : ℝ) * (gap0^2 * gap2^2 * gap3^2) + (2 : ℝ) * (gap0^2 * gap2^1 * gap3^3) + (20 : ℝ) * (gap0^1 * gap1^5) + (52 : ℝ) * (gap0^1 * gap1^4 * gap2^1) + (26 : ℝ) * (gap0^1 * gap1^4 * gap3^1) + (44 : ℝ) * (gap0^1 * gap1^3 * gap2^2) + (44 : ℝ) * (gap0^1 * gap1^3 * gap2^1 * gap3^1) + (14 : ℝ) * (gap0^1 * gap1^3 * gap3^2) + (12 : ℝ) * (gap0^1 * gap1^2 * gap2^3) + (18 : ℝ) * (gap0^1 * gap1^2 * gap2^2 * gap3^1) + (14 : ℝ) * (gap0^1 * gap1^2 * gap2^1 * gap3^2) + (4 : ℝ) * (gap0^1 * gap1^2 * gap3^3) + (2 : ℝ) * (gap0^1 * gap1^1 * gap2^2 * gap3^2) + (2 : ℝ) * (gap0^1 * gap1^1 * gap2^1 * gap3^3) + (4 : ℝ) * (gap1^6) + (14 : ℝ) * (gap1^5 * gap2^1) + (7 : ℝ) * (gap1^5 * gap3^1) + (18 : ℝ) * (gap1^4 * gap2^2) + (18 : ℝ) * (gap1^4 * gap2^1 * gap3^1) + (4 : ℝ) * (gap1^4 * gap3^2) + (10 : ℝ) * (gap1^3 * gap2^3) + (15 : ℝ) * (gap1^3 * gap2^2 * gap3^1) + (7 : ℝ) * (gap1^3 * gap2^1 * gap3^2) + (1 : ℝ) * (gap1^3 * gap3^3) + (2 : ℝ) * (gap1^2 * gap2^4) + (4 : ℝ) * (gap1^2 * gap2^3 * gap3^1) + (3 : ℝ) * (gap1^2 * gap2^2 * gap3^2) + (1 : ℝ) * (gap1^2 * gap2^1 * gap3^3) := by positivity
  convert hpos using 1 <;> ring
theorem solution (a b c d : ℝ) (hab : 0 < a) (hbc : 0 < b) (hcd : 0 < c) (hda : 0 < d) : (a * b / (a + b) + b * c / (b + c) + c * d / (c + d) + d * a / (d + a)) ≤ (2 * (a * b + b * c + c * d + d * a)) / (a + b + c + d)  := by
  have haux0 (a b c d : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) (hord3 : c ≤ d) : 0 ≤ (a^3*b^2*c + a^3*b^2*d + a^3*b*d^2 + a^3*c*d^2 + a^2*b^3*c + a^2*b^3*d - 2*a^2*b^2*c*d - 4*a^2*b*c^2*d - 2*a^2*b*c*d^2 + a^2*b*d^3 + a^2*c*d^3 + a*b^3*c^2 + a*b^2*c^3 - 2*a*b^2*c^2*d - 4*a*b^2*c*d^2 - 2*a*b*c^2*d^2 + a*c^3*d^2 + a*c^2*d^3 + b^3*c^2*d + b^2*c^3*d + b*c^3*d^2 + b*c^2*d^3) := by
    have hd1 : 0 ≤ b - a := by linarith only [hord1]
    have hd2 : 0 ≤ c - b := by linarith only [hord2]
    have hd3 : 0 ≤ d - c := by linarith only [hord3]
    have hi := p2mIndependent0 a (b - a) (c - b) (d - c) hlow hd1 hd2 hd3
    convert hi using 1 <;> ring
  have haux1 (a b c d : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ d) (hord3 : d ≤ c) : 0 ≤ (a^3*b^2*c + a^3*b^2*d + a^3*b*d^2 + a^3*c*d^2 + a^2*b^3*c + a^2*b^3*d - 2*a^2*b^2*c*d - 4*a^2*b*c^2*d - 2*a^2*b*c*d^2 + a^2*b*d^3 + a^2*c*d^3 + a*b^3*c^2 + a*b^2*c^3 - 2*a*b^2*c^2*d - 4*a*b^2*c*d^2 - 2*a*b*c^2*d^2 + a*c^3*d^2 + a*c^2*d^3 + b^3*c^2*d + b^2*c^3*d + b*c^3*d^2 + b*c^2*d^3) := by
    have hd1 : 0 ≤ b - a := by linarith only [hord1]
    have hd2 : 0 ≤ d - b := by linarith only [hord2]
    have hd3 : 0 ≤ c - d := by linarith only [hord3]
    have hi := p2mIndependent1 a (b - a) (d - b) (c - d) hlow hd1 hd2 hd3
    convert hi using 1 <;> ring
  have haux2 (a b c d : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) (hord3 : b ≤ d) : 0 ≤ (a^3*b^2*c + a^3*b^2*d + a^3*b*d^2 + a^3*c*d^2 + a^2*b^3*c + a^2*b^3*d - 2*a^2*b^2*c*d - 4*a^2*b*c^2*d - 2*a^2*b*c*d^2 + a^2*b*d^3 + a^2*c*d^3 + a*b^3*c^2 + a*b^2*c^3 - 2*a*b^2*c^2*d - 4*a*b^2*c*d^2 - 2*a*b*c^2*d^2 + a*c^3*d^2 + a*c^2*d^3 + b^3*c^2*d + b^2*c^3*d + b*c^3*d^2 + b*c^2*d^3) := by
    have hd1 : 0 ≤ c - a := by linarith only [hord1]
    have hd2 : 0 ≤ b - c := by linarith only [hord2]
    have hd3 : 0 ≤ d - b := by linarith only [hord3]
    have hi := p2mIndependent2 a (c - a) (b - c) (d - b) hlow hd1 hd2 hd3
    convert hi using 1 <;> ring
  have hp : 0 ≤ (a^3*b^2*c + a^3*b^2*d + a^3*b*d^2 + a^3*c*d^2 + a^2*b^3*c + a^2*b^3*d - 2*a^2*b^2*c*d - 4*a^2*b*c^2*d - 2*a^2*b*c*d^2 + a^2*b*d^3 + a^2*c*d^3 + a*b^3*c^2 + a*b^2*c^3 - 2*a*b^2*c^2*d - 4*a*b^2*c*d^2 - 2*a*b*c^2*d^2 + a*c^3*d^2 + a*c^2*d^3 + b^3*c^2*d + b^2*c^3*d + b*c^3*d^2 + b*c^2*d^3) := by
    rcases le_total b a with hcase1 | hcase1
    ·
      rcases le_total c b with hcase2 | hcase2
      ·
        rcases le_total d c with hcase3 | hcase3
        ·
          convert haux0 d c b a (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
        ·
          rcases le_total d b with hcase4 | hcase4
          ·
            convert haux1 c d a b (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          ·
            rcases le_total d a with hcase5 | hcase5
            ·
              convert haux1 c b a d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              convert haux0 c b a d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
      ·
        rcases le_total c a with hcase6 | hcase6
        ·
          rcases le_total d b with hcase7 | hcase7
          ·
            convert haux2 d c b a (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          ·
            rcases le_total d c with hcase8 | hcase8
            ·
              convert haux2 b c d a (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              rcases le_total d a with hcase9 | hcase9
              ·
                convert haux0 b c d a (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
              ·
                convert haux1 b c d a (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
        ·
          rcases le_total d b with hcase10 | hcase10
          ·
            convert haux2 d a b c (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          ·
            rcases le_total d a with hcase11 | hcase11
            ·
              convert haux2 b a d c (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              rcases le_total d c with hcase12 | hcase12
              ·
                convert haux0 b a d c (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
              ·
                convert haux1 b a d c (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
    ·
      rcases le_total c a with hcase13 | hcase13
      ·
        rcases le_total d c with hcase14 | hcase14
        ·
          convert haux1 d c b a (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
        ·
          rcases le_total d a with hcase15 | hcase15
          ·
            convert haux0 c d a b (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          ·
            rcases le_total d b with hcase16 | hcase16
            ·
              convert haux2 c d a b (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              convert haux2 c b a d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
      ·
        rcases le_total c b with hcase17 | hcase17
        ·
          rcases le_total d a with hcase18 | hcase18
          ·
            convert haux1 d a b c (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          ·
            rcases le_total d c with hcase19 | hcase19
            ·
              convert haux0 a d c b (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              rcases le_total d b with hcase20 | hcase20
              ·
                convert haux2 a d c b (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
              ·
                convert haux2 a b c d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
        ·
          rcases le_total d a with hcase21 | hcase21
          ·
            convert haux0 d a b c (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          ·
            rcases le_total d b with hcase22 | hcase22
            ·
              convert haux1 a d c b (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              rcases le_total d c with hcase23 | hcase23
              ·
                convert haux1 a b c d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
              ·
                convert haux0 a b c d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
  have hn : 0 ≤ (a^3*b^2*c + a^3*b^2*d + a^3*b*d^2 + a^3*c*d^2 + a^2*b^3*c + a^2*b^3*d - 2*a^2*b^2*c*d - 4*a^2*b*c^2*d - 2*a^2*b*c*d^2 + a^2*b*d^3 + a^2*c*d^3 + a*b^3*c^2 + a*b^2*c^3 - 2*a*b^2*c^2*d - 4*a*b^2*c*d^2 - 2*a*b*c^2*d^2 + a*c^3*d^2 + a*c^2*d^3 + b^3*c^2*d + b^2*c^3*d + b*c^3*d^2 + b*c^2*d^3) := by nlinarith only [hp]
  have hd : (0 : ℝ) < ((a + b)*(a + d)*(b + c)*(c + d)*(a + b + c + d)) := by positivity
  have heqrat : ( (2 * (a * b + b * c + c * d + d * a)) / (a + b + c + d)  ) - ( (a * b / (a + b) + b * c / (b + c) + c * d / (c + d) + d * a / (d + a)) ) = (a^3*b^2*c + a^3*b^2*d + a^3*b*d^2 + a^3*c*d^2 + a^2*b^3*c + a^2*b^3*d - 2*a^2*b^2*c*d - 4*a^2*b*c^2*d - 2*a^2*b*c*d^2 + a^2*b*d^3 + a^2*c*d^3 + a*b^3*c^2 + a*b^2*c^3 - 2*a*b^2*c^2*d - 4*a*b^2*c*d^2 - 2*a*b*c^2*d^2 + a*c^3*d^2 + a*c^2*d^3 + b^3*c^2*d + b^2*c^3*d + b*c^3*d^2 + b*c^2*d^3) / ((a + b)*(a + d)*(b + c)*(c + d)*(a + b + c + d)) := by
    field_simp (disch := positivity)
    <;> ring
  have hfrac := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hfrac]
example : (∀ (a b c d : ℝ) (hab : 0 < a) (hbc : 0 < b) (hcd : 0 < c) (hda : 0 < d), (a * b / (a + b) + b * c / (b + c) + c * d / (c + d) + d * a / (d + a)) ≤ (2 * (a * b + b * c + c * d + d * a)) / (a + b + c + d)) := @solution
#print axioms solution
