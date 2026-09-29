-- Prove2me | solution 1 for WorkbookSource.base_16402
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T11:39:57.996208+00:00
-- url     : https://prove2.me/submissions/1b354698-57a8-4a28-9af6-6400e00d1189

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
private lemma p2mIndependent0 (gap0 gap1 gap2 gap3 : ℝ) (hg0 : 0 ≤ gap0) (hg1 : 0 ≤ gap1) (hg2 : 0 ≤ gap2) (hg3 : 0 ≤ gap3) : 0 ≤ (9*(gap0)^3*(gap0 + gap1 + gap2) + 3*(gap0)^3*(gap0 + gap1 + gap2 + gap3) + 9*(gap0)^2*(gap0 + gap1)^2 - 21*(gap0)^2*(gap0 + gap1)*(gap0 + gap1 + gap2) - 8*(gap0)^2*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3) - 9*(gap0)^2*(gap0 + gap1 + gap2)^2 + 24*(gap0)^2*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3) + 9*(gap0)^2*(gap0 + gap1 + gap2 + gap3)^2 + 3*(gap0)*(gap0 + gap1)^3 - 8*(gap0)*(gap0 + gap1)^2*(gap0 + gap1 + gap2) + 24*(gap0)*(gap0 + gap1)^2*(gap0 + gap1 + gap2 + gap3) + 24*(gap0)*(gap0 + gap1)*(gap0 + gap1 + gap2)^2 - 46*(gap0)*(gap0 + gap1)*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3) - 21*(gap0)*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3)^2 + 9*(gap0)*(gap0 + gap1 + gap2)^3 - 21*(gap0)*(gap0 + gap1 + gap2)^2*(gap0 + gap1 + gap2 + gap3) - 8*(gap0)*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3)^2 + 9*(gap0 + gap1)^3*(gap0 + gap1 + gap2 + gap3) + 9*(gap0 + gap1)^2*(gap0 + gap1 + gap2)^2 - 21*(gap0 + gap1)^2*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3) - 9*(gap0 + gap1)^2*(gap0 + gap1 + gap2 + gap3)^2 + 3*(gap0 + gap1)*(gap0 + gap1 + gap2)^3 - 8*(gap0 + gap1)*(gap0 + gap1 + gap2)^2*(gap0 + gap1 + gap2 + gap3) + 24*(gap0 + gap1)*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3)^2 + 9*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3)^3 + 9*(gap0 + gap1 + gap2)^2*(gap0 + gap1 + gap2 + gap3)^2 + 3*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3)^3) := by
  have hpos : 0 ≤ (40 : ℝ) * (gap0^2 * gap1^2) + (56 : ℝ) * (gap0^2 * gap1^1 * gap2^1) + (24 : ℝ) * (gap0^2 * gap1^1 * gap3^1) + (56 : ℝ) * (gap0^2 * gap2^2) + (56 : ℝ) * (gap0^2 * gap2^1 * gap3^1) + (40 : ℝ) * (gap0^2 * gap3^2) + (68 : ℝ) * (gap0^1 * gap1^3) + (167 : ℝ) * (gap0^1 * gap1^2 * gap2^1) + (91 : ℝ) * (gap0^1 * gap1^2 * gap3^1) + (167 : ℝ) * (gap0^1 * gap1^1 * gap2^2) + (190 : ℝ) * (gap0^1 * gap1^1 * gap2^1 * gap3^1) + (91 : ℝ) * (gap0^1 * gap1^1 * gap3^2) + (56 : ℝ) * (gap0^1 * gap2^3) + (111 : ℝ) * (gap0^1 * gap2^2 * gap3^1) + (79 : ℝ) * (gap0^1 * gap2^1 * gap3^2) + (12 : ℝ) * (gap0^1 * gap3^3) + (28 : ℝ) * (gap1^4) + (99 : ℝ) * (gap1^3 * gap2^1) + (64 : ℝ) * (gap1^3 * gap3^1) + (135 : ℝ) * (gap1^2 * gap2^2) + (176 : ℝ) * (gap1^2 * gap2^1 * gap3^1) + (60 : ℝ) * (gap1^2 * gap3^2) + (76 : ℝ) * (gap1^1 * gap2^3) + (148 : ℝ) * (gap1^1 * gap2^2 * gap3^1) + (87 : ℝ) * (gap1^1 * gap2^1 * gap3^2) + (12 : ℝ) * (gap1^1 * gap3^3) + (12 : ℝ) * (gap2^4) + (27 : ℝ) * (gap2^3 * gap3^1) + (18 : ℝ) * (gap2^2 * gap3^2) + (3 : ℝ) * (gap2^1 * gap3^3) := by positivity
  convert hpos using 1 <;> ring

private lemma p2mIndependent1 (gap0 gap1 gap2 gap3 : ℝ) (hg0 : 0 ≤ gap0) (hg1 : 0 ≤ gap1) (hg2 : 0 ≤ gap2) (hg3 : 0 ≤ gap3) : 0 ≤ (9*(gap0)^3*(gap0 + gap1 + gap2 + gap3) + 3*(gap0)^3*(gap0 + gap1 + gap2) + 9*(gap0)^2*(gap0 + gap1)^2 - 21*(gap0)^2*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3) - 8*(gap0)^2*(gap0 + gap1)*(gap0 + gap1 + gap2) - 9*(gap0)^2*(gap0 + gap1 + gap2 + gap3)^2 + 24*(gap0)^2*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1 + gap2) + 9*(gap0)^2*(gap0 + gap1 + gap2)^2 + 3*(gap0)*(gap0 + gap1)^3 - 8*(gap0)*(gap0 + gap1)^2*(gap0 + gap1 + gap2 + gap3) + 24*(gap0)*(gap0 + gap1)^2*(gap0 + gap1 + gap2) + 24*(gap0)*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3)^2 - 46*(gap0)*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1 + gap2) - 21*(gap0)*(gap0 + gap1)*(gap0 + gap1 + gap2)^2 + 9*(gap0)*(gap0 + gap1 + gap2 + gap3)^3 - 21*(gap0)*(gap0 + gap1 + gap2 + gap3)^2*(gap0 + gap1 + gap2) - 8*(gap0)*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1 + gap2)^2 + 9*(gap0 + gap1)^3*(gap0 + gap1 + gap2) + 9*(gap0 + gap1)^2*(gap0 + gap1 + gap2 + gap3)^2 - 21*(gap0 + gap1)^2*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1 + gap2) - 9*(gap0 + gap1)^2*(gap0 + gap1 + gap2)^2 + 3*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3)^3 - 8*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3)^2*(gap0 + gap1 + gap2) + 24*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1 + gap2)^2 + 9*(gap0 + gap1)*(gap0 + gap1 + gap2)^3 + 9*(gap0 + gap1 + gap2 + gap3)^2*(gap0 + gap1 + gap2)^2 + 3*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1 + gap2)^3) := by
  have hpos : 0 ≤ (40 : ℝ) * (gap0^2 * gap1^2) + (56 : ℝ) * (gap0^2 * gap1^1 * gap2^1) + (32 : ℝ) * (gap0^2 * gap1^1 * gap3^1) + (56 : ℝ) * (gap0^2 * gap2^2) + (56 : ℝ) * (gap0^2 * gap2^1 * gap3^1) + (40 : ℝ) * (gap0^2 * gap3^2) + (68 : ℝ) * (gap0^1 * gap1^3) + (167 : ℝ) * (gap0^1 * gap1^2 * gap2^1) + (76 : ℝ) * (gap0^1 * gap1^2 * gap3^1) + (167 : ℝ) * (gap0^1 * gap1^1 * gap2^2) + (144 : ℝ) * (gap0^1 * gap1^1 * gap2^1 * gap3^1) + (68 : ℝ) * (gap0^1 * gap1^1 * gap3^2) + (56 : ℝ) * (gap0^1 * gap2^3) + (57 : ℝ) * (gap0^1 * gap2^2 * gap3^1) + (25 : ℝ) * (gap0^1 * gap2^1 * gap3^2) + (12 : ℝ) * (gap0^1 * gap3^3) + (28 : ℝ) * (gap1^4) + (99 : ℝ) * (gap1^3 * gap2^1) + (35 : ℝ) * (gap1^3 * gap3^1) + (135 : ℝ) * (gap1^2 * gap2^2) + (94 : ℝ) * (gap1^2 * gap2^1 * gap3^1) + (19 : ℝ) * (gap1^2 * gap3^2) + (76 : ℝ) * (gap1^1 * gap2^3) + (80 : ℝ) * (gap1^1 * gap2^2 * gap3^1) + (19 : ℝ) * (gap1^1 * gap2^1 * gap3^2) + (3 : ℝ) * (gap1^1 * gap3^3) + (12 : ℝ) * (gap2^4) + (21 : ℝ) * (gap2^3 * gap3^1) + (9 : ℝ) * (gap2^2 * gap3^2) := by positivity
  convert hpos using 1 <;> ring

private lemma p2mIndependent2 (gap0 gap1 gap2 gap3 : ℝ) (hg0 : 0 ≤ gap0) (hg1 : 0 ≤ gap1) (hg2 : 0 ≤ gap2) (hg3 : 0 ≤ gap3) : 0 ≤ (9*(gap0)^3*(gap0 + gap1) + 3*(gap0)^3*(gap0 + gap1 + gap2 + gap3) + 9*(gap0)^2*(gap0 + gap1 + gap2)^2 - 21*(gap0)^2*(gap0 + gap1 + gap2)*(gap0 + gap1) - 8*(gap0)^2*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3) - 9*(gap0)^2*(gap0 + gap1)^2 + 24*(gap0)^2*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3) + 9*(gap0)^2*(gap0 + gap1 + gap2 + gap3)^2 + 3*(gap0)*(gap0 + gap1 + gap2)^3 - 8*(gap0)*(gap0 + gap1 + gap2)^2*(gap0 + gap1) + 24*(gap0)*(gap0 + gap1 + gap2)^2*(gap0 + gap1 + gap2 + gap3) + 24*(gap0)*(gap0 + gap1 + gap2)*(gap0 + gap1)^2 - 46*(gap0)*(gap0 + gap1 + gap2)*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3) - 21*(gap0)*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3)^2 + 9*(gap0)*(gap0 + gap1)^3 - 21*(gap0)*(gap0 + gap1)^2*(gap0 + gap1 + gap2 + gap3) - 8*(gap0)*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3)^2 + 9*(gap0 + gap1 + gap2)^3*(gap0 + gap1 + gap2 + gap3) + 9*(gap0 + gap1 + gap2)^2*(gap0 + gap1)^2 - 21*(gap0 + gap1 + gap2)^2*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3) - 9*(gap0 + gap1 + gap2)^2*(gap0 + gap1 + gap2 + gap3)^2 + 3*(gap0 + gap1 + gap2)*(gap0 + gap1)^3 - 8*(gap0 + gap1 + gap2)*(gap0 + gap1)^2*(gap0 + gap1 + gap2 + gap3) + 24*(gap0 + gap1 + gap2)*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3)^2 + 9*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3)^3 + 9*(gap0 + gap1)^2*(gap0 + gap1 + gap2 + gap3)^2 + 3*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3)^3) := by
  have hpos : 0 ≤ (40 : ℝ) * (gap0^2 * gap1^2) + (48 : ℝ) * (gap0^2 * gap1^1 * gap2^1) + (24 : ℝ) * (gap0^2 * gap1^1 * gap3^1) + (48 : ℝ) * (gap0^2 * gap2^2) + (48 : ℝ) * (gap0^2 * gap2^1 * gap3^1) + (40 : ℝ) * (gap0^2 * gap3^2) + (68 : ℝ) * (gap0^1 * gap1^3) + (128 : ℝ) * (gap0^1 * gap1^2 * gap2^1) + (91 : ℝ) * (gap0^1 * gap1^2 * gap3^1) + (120 : ℝ) * (gap0^1 * gap1^1 * gap2^2) + (174 : ℝ) * (gap0^1 * gap1^1 * gap2^1 * gap3^1) + (91 : ℝ) * (gap0^1 * gap1^1 * gap3^2) + (48 : ℝ) * (gap0^1 * gap2^3) + (72 : ℝ) * (gap0^1 * gap2^2 * gap3^1) + (48 : ℝ) * (gap0^1 * gap2^1 * gap3^2) + (12 : ℝ) * (gap0^1 * gap3^3) + (28 : ℝ) * (gap1^4) + (77 : ℝ) * (gap1^3 * gap2^1) + (64 : ℝ) * (gap1^3 * gap3^1) + (82 : ℝ) * (gap1^2 * gap2^2) + (136 : ℝ) * (gap1^2 * gap2^1 * gap3^1) + (60 : ℝ) * (gap1^2 * gap3^2) + (42 : ℝ) * (gap1^1 * gap2^3) + (90 : ℝ) * (gap1^1 * gap2^2 * gap3^1) + (69 : ℝ) * (gap1^1 * gap2^1 * gap3^2) + (12 : ℝ) * (gap1^1 * gap3^3) + (9 : ℝ) * (gap2^4) + (18 : ℝ) * (gap2^3 * gap3^1) + (18 : ℝ) * (gap2^2 * gap3^2) + (9 : ℝ) * (gap2^1 * gap3^3) := by positivity
  convert hpos using 1 <;> ring

private lemma p2mIndependent3 (gap0 gap1 gap2 gap3 : ℝ) (hg0 : 0 ≤ gap0) (hg1 : 0 ≤ gap1) (hg2 : 0 ≤ gap2) (hg3 : 0 ≤ gap3) : 0 ≤ (9*(gap0)^3*(gap0 + gap1) + 3*(gap0)^3*(gap0 + gap1 + gap2) + 9*(gap0)^2*(gap0 + gap1 + gap2 + gap3)^2 - 21*(gap0)^2*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1) - 8*(gap0)^2*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1 + gap2) - 9*(gap0)^2*(gap0 + gap1)^2 + 24*(gap0)^2*(gap0 + gap1)*(gap0 + gap1 + gap2) + 9*(gap0)^2*(gap0 + gap1 + gap2)^2 + 3*(gap0)*(gap0 + gap1 + gap2 + gap3)^3 - 8*(gap0)*(gap0 + gap1 + gap2 + gap3)^2*(gap0 + gap1) + 24*(gap0)*(gap0 + gap1 + gap2 + gap3)^2*(gap0 + gap1 + gap2) + 24*(gap0)*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1)^2 - 46*(gap0)*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1)*(gap0 + gap1 + gap2) - 21*(gap0)*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1 + gap2)^2 + 9*(gap0)*(gap0 + gap1)^3 - 21*(gap0)*(gap0 + gap1)^2*(gap0 + gap1 + gap2) - 8*(gap0)*(gap0 + gap1)*(gap0 + gap1 + gap2)^2 + 9*(gap0 + gap1 + gap2 + gap3)^3*(gap0 + gap1 + gap2) + 9*(gap0 + gap1 + gap2 + gap3)^2*(gap0 + gap1)^2 - 21*(gap0 + gap1 + gap2 + gap3)^2*(gap0 + gap1)*(gap0 + gap1 + gap2) - 9*(gap0 + gap1 + gap2 + gap3)^2*(gap0 + gap1 + gap2)^2 + 3*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1)^3 - 8*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1)^2*(gap0 + gap1 + gap2) + 24*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1)*(gap0 + gap1 + gap2)^2 + 9*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1 + gap2)^3 + 9*(gap0 + gap1)^2*(gap0 + gap1 + gap2)^2 + 3*(gap0 + gap1)*(gap0 + gap1 + gap2)^3) := by
  have hpos : 0 ≤ (40 : ℝ) * (gap0^2 * gap1^2) + (48 : ℝ) * (gap0^2 * gap1^1 * gap2^1) + (24 : ℝ) * (gap0^2 * gap1^1 * gap3^1) + (48 : ℝ) * (gap0^2 * gap2^2) + (48 : ℝ) * (gap0^2 * gap2^1 * gap3^1) + (40 : ℝ) * (gap0^2 * gap3^2) + (68 : ℝ) * (gap0^1 * gap1^3) + (128 : ℝ) * (gap0^1 * gap1^2 * gap2^1) + (37 : ℝ) * (gap0^1 * gap1^2 * gap3^1) + (120 : ℝ) * (gap0^1 * gap1^1 * gap2^2) + (66 : ℝ) * (gap0^1 * gap1^1 * gap2^1 * gap3^1) + (37 : ℝ) * (gap0^1 * gap1^1 * gap3^2) + (48 : ℝ) * (gap0^1 * gap2^3) + (72 : ℝ) * (gap0^1 * gap2^2 * gap3^1) + (48 : ℝ) * (gap0^1 * gap2^1 * gap3^2) + (12 : ℝ) * (gap0^1 * gap3^3) + (28 : ℝ) * (gap1^4) + (77 : ℝ) * (gap1^3 * gap2^1) + (13 : ℝ) * (gap1^3 * gap3^1) + (82 : ℝ) * (gap1^2 * gap2^2) + (28 : ℝ) * (gap1^2 * gap2^1 * gap3^1) + (6 : ℝ) * (gap1^2 * gap3^2) + (42 : ℝ) * (gap1^1 * gap2^3) + (36 : ℝ) * (gap1^1 * gap2^2 * gap3^1) + (15 : ℝ) * (gap1^1 * gap2^1 * gap3^2) + (9 : ℝ) * (gap1^1 * gap3^3) + (9 : ℝ) * (gap2^4) + (18 : ℝ) * (gap2^3 * gap3^1) + (18 : ℝ) * (gap2^2 * gap3^2) + (9 : ℝ) * (gap2^1 * gap3^3) := by positivity
  convert hpos using 1 <;> ring

private lemma p2mIndependent4 (gap0 gap1 gap2 gap3 : ℝ) (hg0 : 0 ≤ gap0) (hg1 : 0 ≤ gap1) (hg2 : 0 ≤ gap2) (hg3 : 0 ≤ gap3) : 0 ≤ (9*(gap0)^3*(gap0 + gap1 + gap2 + gap3) + 3*(gap0)^3*(gap0 + gap1) + 9*(gap0)^2*(gap0 + gap1 + gap2)^2 - 21*(gap0)^2*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3) - 8*(gap0)^2*(gap0 + gap1 + gap2)*(gap0 + gap1) - 9*(gap0)^2*(gap0 + gap1 + gap2 + gap3)^2 + 24*(gap0)^2*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1) + 9*(gap0)^2*(gap0 + gap1)^2 + 3*(gap0)*(gap0 + gap1 + gap2)^3 - 8*(gap0)*(gap0 + gap1 + gap2)^2*(gap0 + gap1 + gap2 + gap3) + 24*(gap0)*(gap0 + gap1 + gap2)^2*(gap0 + gap1) + 24*(gap0)*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3)^2 - 46*(gap0)*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1) - 21*(gap0)*(gap0 + gap1 + gap2)*(gap0 + gap1)^2 + 9*(gap0)*(gap0 + gap1 + gap2 + gap3)^3 - 21*(gap0)*(gap0 + gap1 + gap2 + gap3)^2*(gap0 + gap1) - 8*(gap0)*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1)^2 + 9*(gap0 + gap1 + gap2)^3*(gap0 + gap1) + 9*(gap0 + gap1 + gap2)^2*(gap0 + gap1 + gap2 + gap3)^2 - 21*(gap0 + gap1 + gap2)^2*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1) - 9*(gap0 + gap1 + gap2)^2*(gap0 + gap1)^2 + 3*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3)^3 - 8*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3)^2*(gap0 + gap1) + 24*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1)^2 + 9*(gap0 + gap1 + gap2)*(gap0 + gap1)^3 + 9*(gap0 + gap1 + gap2 + gap3)^2*(gap0 + gap1)^2 + 3*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1)^3) := by
  have hpos : 0 ≤ (40 : ℝ) * (gap0^2 * gap1^2) + (56 : ℝ) * (gap0^2 * gap1^1 * gap2^1) + (32 : ℝ) * (gap0^2 * gap1^1 * gap3^1) + (56 : ℝ) * (gap0^2 * gap2^2) + (56 : ℝ) * (gap0^2 * gap2^1 * gap3^1) + (40 : ℝ) * (gap0^2 * gap3^2) + (68 : ℝ) * (gap0^1 * gap1^3) + (113 : ℝ) * (gap0^1 * gap1^2 * gap2^1) + (76 : ℝ) * (gap0^1 * gap1^2 * gap3^1) + (113 : ℝ) * (gap0^1 * gap1^1 * gap2^2) + (144 : ℝ) * (gap0^1 * gap1^1 * gap2^1 * gap3^1) + (68 : ℝ) * (gap0^1 * gap1^1 * gap3^2) + (56 : ℝ) * (gap0^1 * gap2^3) + (111 : ℝ) * (gap0^1 * gap2^2 * gap3^1) + (79 : ℝ) * (gap0^1 * gap2^1 * gap3^2) + (12 : ℝ) * (gap0^1 * gap3^3) + (28 : ℝ) * (gap1^4) + (48 : ℝ) * (gap1^3 * gap2^1) + (35 : ℝ) * (gap1^3 * gap3^1) + (36 : ℝ) * (gap1^2 * gap2^2) + (49 : ℝ) * (gap1^2 * gap2^1 * gap3^1) + (19 : ℝ) * (gap1^2 * gap3^2) + (28 : ℝ) * (gap1^1 * gap2^3) + (44 : ℝ) * (gap1^1 * gap2^2 * gap3^1) + (28 : ℝ) * (gap1^1 * gap2^1 * gap3^2) + (3 : ℝ) * (gap1^1 * gap3^3) + (12 : ℝ) * (gap2^4) + (27 : ℝ) * (gap2^3 * gap3^1) + (18 : ℝ) * (gap2^2 * gap3^2) + (3 : ℝ) * (gap2^1 * gap3^3) := by positivity
  convert hpos using 1 <;> ring

private lemma p2mIndependent5 (gap0 gap1 gap2 gap3 : ℝ) (hg0 : 0 ≤ gap0) (hg1 : 0 ≤ gap1) (hg2 : 0 ≤ gap2) (hg3 : 0 ≤ gap3) : 0 ≤ (9*(gap0)^3*(gap0 + gap1 + gap2) + 3*(gap0)^3*(gap0 + gap1) + 9*(gap0)^2*(gap0 + gap1 + gap2 + gap3)^2 - 21*(gap0)^2*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1 + gap2) - 8*(gap0)^2*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1) - 9*(gap0)^2*(gap0 + gap1 + gap2)^2 + 24*(gap0)^2*(gap0 + gap1 + gap2)*(gap0 + gap1) + 9*(gap0)^2*(gap0 + gap1)^2 + 3*(gap0)*(gap0 + gap1 + gap2 + gap3)^3 - 8*(gap0)*(gap0 + gap1 + gap2 + gap3)^2*(gap0 + gap1 + gap2) + 24*(gap0)*(gap0 + gap1 + gap2 + gap3)^2*(gap0 + gap1) + 24*(gap0)*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1 + gap2)^2 - 46*(gap0)*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1 + gap2)*(gap0 + gap1) - 21*(gap0)*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1)^2 + 9*(gap0)*(gap0 + gap1 + gap2)^3 - 21*(gap0)*(gap0 + gap1 + gap2)^2*(gap0 + gap1) - 8*(gap0)*(gap0 + gap1 + gap2)*(gap0 + gap1)^2 + 9*(gap0 + gap1 + gap2 + gap3)^3*(gap0 + gap1) + 9*(gap0 + gap1 + gap2 + gap3)^2*(gap0 + gap1 + gap2)^2 - 21*(gap0 + gap1 + gap2 + gap3)^2*(gap0 + gap1 + gap2)*(gap0 + gap1) - 9*(gap0 + gap1 + gap2 + gap3)^2*(gap0 + gap1)^2 + 3*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1 + gap2)^3 - 8*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1 + gap2)^2*(gap0 + gap1) + 24*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1 + gap2)*(gap0 + gap1)^2 + 9*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1)^3 + 9*(gap0 + gap1 + gap2)^2*(gap0 + gap1)^2 + 3*(gap0 + gap1 + gap2)*(gap0 + gap1)^3) := by
  have hpos : 0 ≤ (40 : ℝ) * (gap0^2 * gap1^2) + (56 : ℝ) * (gap0^2 * gap1^1 * gap2^1) + (24 : ℝ) * (gap0^2 * gap1^1 * gap3^1) + (56 : ℝ) * (gap0^2 * gap2^2) + (56 : ℝ) * (gap0^2 * gap2^1 * gap3^1) + (40 : ℝ) * (gap0^2 * gap3^2) + (68 : ℝ) * (gap0^1 * gap1^3) + (113 : ℝ) * (gap0^1 * gap1^2 * gap2^1) + (37 : ℝ) * (gap0^1 * gap1^2 * gap3^1) + (113 : ℝ) * (gap0^1 * gap1^1 * gap2^2) + (82 : ℝ) * (gap0^1 * gap1^1 * gap2^1 * gap3^1) + (37 : ℝ) * (gap0^1 * gap1^1 * gap3^2) + (56 : ℝ) * (gap0^1 * gap2^3) + (57 : ℝ) * (gap0^1 * gap2^2 * gap3^1) + (25 : ℝ) * (gap0^1 * gap2^1 * gap3^2) + (12 : ℝ) * (gap0^1 * gap3^3) + (28 : ℝ) * (gap1^4) + (48 : ℝ) * (gap1^3 * gap2^1) + (13 : ℝ) * (gap1^3 * gap3^1) + (36 : ℝ) * (gap1^2 * gap2^2) + (23 : ℝ) * (gap1^2 * gap2^1 * gap3^1) + (6 : ℝ) * (gap1^2 * gap3^2) + (28 : ℝ) * (gap1^1 * gap2^3) + (40 : ℝ) * (gap1^1 * gap2^2 * gap3^1) + (24 : ℝ) * (gap1^1 * gap2^1 * gap3^2) + (9 : ℝ) * (gap1^1 * gap3^3) + (12 : ℝ) * (gap2^4) + (21 : ℝ) * (gap2^3 * gap3^1) + (9 : ℝ) * (gap2^2 * gap3^2) := by positivity
  convert hpos using 1 <;> ring
theorem solution (x1 x2 x3 x4 : ℝ) (hx1 : 0 < x1) (hx2 : 0 < x2) (hx3 : 0 < x3) (hx4 : 0 < x4) : (x1 / (3 * x2 + x3) + x2 / (3 * x3 + x4) + x3 / (3 * x4 + x1) + x4 / (3 * x1 + x2)) ≥ 1  := by
  have haux0 (x1 x2 x3 x4 : ℝ) (hlow : 0 ≤ x1) (hord1 : x1 ≤ x2) (hord2 : x2 ≤ x3) (hord3 : x3 ≤ x4) : 0 ≤ (9*x1^3*x3 + 3*x1^3*x4 + 9*x1^2*x2^2 - 21*x1^2*x2*x3 - 8*x1^2*x2*x4 - 9*x1^2*x3^2 + 24*x1^2*x3*x4 + 9*x1^2*x4^2 + 3*x1*x2^3 - 8*x1*x2^2*x3 + 24*x1*x2^2*x4 + 24*x1*x2*x3^2 - 46*x1*x2*x3*x4 - 21*x1*x2*x4^2 + 9*x1*x3^3 - 21*x1*x3^2*x4 - 8*x1*x3*x4^2 + 9*x2^3*x4 + 9*x2^2*x3^2 - 21*x2^2*x3*x4 - 9*x2^2*x4^2 + 3*x2*x3^3 - 8*x2*x3^2*x4 + 24*x2*x3*x4^2 + 9*x2*x4^3 + 9*x3^2*x4^2 + 3*x3*x4^3) := by
    have hd1 : 0 ≤ x2 - x1 := by linarith only [hord1]
    have hd2 : 0 ≤ x3 - x2 := by linarith only [hord2]
    have hd3 : 0 ≤ x4 - x3 := by linarith only [hord3]
    have hi := p2mIndependent0 x1 (x2 - x1) (x3 - x2) (x4 - x3) hlow hd1 hd2 hd3
    convert hi using 1 <;> ring
  have haux1 (x1 x2 x3 x4 : ℝ) (hlow : 0 ≤ x1) (hord1 : x1 ≤ x2) (hord2 : x2 ≤ x4) (hord3 : x4 ≤ x3) : 0 ≤ (9*x1^3*x3 + 3*x1^3*x4 + 9*x1^2*x2^2 - 21*x1^2*x2*x3 - 8*x1^2*x2*x4 - 9*x1^2*x3^2 + 24*x1^2*x3*x4 + 9*x1^2*x4^2 + 3*x1*x2^3 - 8*x1*x2^2*x3 + 24*x1*x2^2*x4 + 24*x1*x2*x3^2 - 46*x1*x2*x3*x4 - 21*x1*x2*x4^2 + 9*x1*x3^3 - 21*x1*x3^2*x4 - 8*x1*x3*x4^2 + 9*x2^3*x4 + 9*x2^2*x3^2 - 21*x2^2*x3*x4 - 9*x2^2*x4^2 + 3*x2*x3^3 - 8*x2*x3^2*x4 + 24*x2*x3*x4^2 + 9*x2*x4^3 + 9*x3^2*x4^2 + 3*x3*x4^3) := by
    have hd1 : 0 ≤ x2 - x1 := by linarith only [hord1]
    have hd2 : 0 ≤ x4 - x2 := by linarith only [hord2]
    have hd3 : 0 ≤ x3 - x4 := by linarith only [hord3]
    have hi := p2mIndependent1 x1 (x2 - x1) (x4 - x2) (x3 - x4) hlow hd1 hd2 hd3
    convert hi using 1 <;> ring
  have haux2 (x1 x2 x3 x4 : ℝ) (hlow : 0 ≤ x1) (hord1 : x1 ≤ x3) (hord2 : x3 ≤ x2) (hord3 : x2 ≤ x4) : 0 ≤ (9*x1^3*x3 + 3*x1^3*x4 + 9*x1^2*x2^2 - 21*x1^2*x2*x3 - 8*x1^2*x2*x4 - 9*x1^2*x3^2 + 24*x1^2*x3*x4 + 9*x1^2*x4^2 + 3*x1*x2^3 - 8*x1*x2^2*x3 + 24*x1*x2^2*x4 + 24*x1*x2*x3^2 - 46*x1*x2*x3*x4 - 21*x1*x2*x4^2 + 9*x1*x3^3 - 21*x1*x3^2*x4 - 8*x1*x3*x4^2 + 9*x2^3*x4 + 9*x2^2*x3^2 - 21*x2^2*x3*x4 - 9*x2^2*x4^2 + 3*x2*x3^3 - 8*x2*x3^2*x4 + 24*x2*x3*x4^2 + 9*x2*x4^3 + 9*x3^2*x4^2 + 3*x3*x4^3) := by
    have hd1 : 0 ≤ x3 - x1 := by linarith only [hord1]
    have hd2 : 0 ≤ x2 - x3 := by linarith only [hord2]
    have hd3 : 0 ≤ x4 - x2 := by linarith only [hord3]
    have hi := p2mIndependent2 x1 (x3 - x1) (x2 - x3) (x4 - x2) hlow hd1 hd2 hd3
    convert hi using 1 <;> ring
  have haux3 (x1 x2 x3 x4 : ℝ) (hlow : 0 ≤ x1) (hord1 : x1 ≤ x3) (hord2 : x3 ≤ x4) (hord3 : x4 ≤ x2) : 0 ≤ (9*x1^3*x3 + 3*x1^3*x4 + 9*x1^2*x2^2 - 21*x1^2*x2*x3 - 8*x1^2*x2*x4 - 9*x1^2*x3^2 + 24*x1^2*x3*x4 + 9*x1^2*x4^2 + 3*x1*x2^3 - 8*x1*x2^2*x3 + 24*x1*x2^2*x4 + 24*x1*x2*x3^2 - 46*x1*x2*x3*x4 - 21*x1*x2*x4^2 + 9*x1*x3^3 - 21*x1*x3^2*x4 - 8*x1*x3*x4^2 + 9*x2^3*x4 + 9*x2^2*x3^2 - 21*x2^2*x3*x4 - 9*x2^2*x4^2 + 3*x2*x3^3 - 8*x2*x3^2*x4 + 24*x2*x3*x4^2 + 9*x2*x4^3 + 9*x3^2*x4^2 + 3*x3*x4^3) := by
    have hd1 : 0 ≤ x3 - x1 := by linarith only [hord1]
    have hd2 : 0 ≤ x4 - x3 := by linarith only [hord2]
    have hd3 : 0 ≤ x2 - x4 := by linarith only [hord3]
    have hi := p2mIndependent3 x1 (x3 - x1) (x4 - x3) (x2 - x4) hlow hd1 hd2 hd3
    convert hi using 1 <;> ring
  have haux4 (x1 x2 x3 x4 : ℝ) (hlow : 0 ≤ x1) (hord1 : x1 ≤ x4) (hord2 : x4 ≤ x2) (hord3 : x2 ≤ x3) : 0 ≤ (9*x1^3*x3 + 3*x1^3*x4 + 9*x1^2*x2^2 - 21*x1^2*x2*x3 - 8*x1^2*x2*x4 - 9*x1^2*x3^2 + 24*x1^2*x3*x4 + 9*x1^2*x4^2 + 3*x1*x2^3 - 8*x1*x2^2*x3 + 24*x1*x2^2*x4 + 24*x1*x2*x3^2 - 46*x1*x2*x3*x4 - 21*x1*x2*x4^2 + 9*x1*x3^3 - 21*x1*x3^2*x4 - 8*x1*x3*x4^2 + 9*x2^3*x4 + 9*x2^2*x3^2 - 21*x2^2*x3*x4 - 9*x2^2*x4^2 + 3*x2*x3^3 - 8*x2*x3^2*x4 + 24*x2*x3*x4^2 + 9*x2*x4^3 + 9*x3^2*x4^2 + 3*x3*x4^3) := by
    have hd1 : 0 ≤ x4 - x1 := by linarith only [hord1]
    have hd2 : 0 ≤ x2 - x4 := by linarith only [hord2]
    have hd3 : 0 ≤ x3 - x2 := by linarith only [hord3]
    have hi := p2mIndependent4 x1 (x4 - x1) (x2 - x4) (x3 - x2) hlow hd1 hd2 hd3
    convert hi using 1 <;> ring
  have haux5 (x1 x2 x3 x4 : ℝ) (hlow : 0 ≤ x1) (hord1 : x1 ≤ x4) (hord2 : x4 ≤ x3) (hord3 : x3 ≤ x2) : 0 ≤ (9*x1^3*x3 + 3*x1^3*x4 + 9*x1^2*x2^2 - 21*x1^2*x2*x3 - 8*x1^2*x2*x4 - 9*x1^2*x3^2 + 24*x1^2*x3*x4 + 9*x1^2*x4^2 + 3*x1*x2^3 - 8*x1*x2^2*x3 + 24*x1*x2^2*x4 + 24*x1*x2*x3^2 - 46*x1*x2*x3*x4 - 21*x1*x2*x4^2 + 9*x1*x3^3 - 21*x1*x3^2*x4 - 8*x1*x3*x4^2 + 9*x2^3*x4 + 9*x2^2*x3^2 - 21*x2^2*x3*x4 - 9*x2^2*x4^2 + 3*x2*x3^3 - 8*x2*x3^2*x4 + 24*x2*x3*x4^2 + 9*x2*x4^3 + 9*x3^2*x4^2 + 3*x3*x4^3) := by
    have hd1 : 0 ≤ x4 - x1 := by linarith only [hord1]
    have hd2 : 0 ≤ x3 - x4 := by linarith only [hord2]
    have hd3 : 0 ≤ x2 - x3 := by linarith only [hord3]
    have hi := p2mIndependent5 x1 (x4 - x1) (x3 - x4) (x2 - x3) hlow hd1 hd2 hd3
    convert hi using 1 <;> ring
  have hp : 0 ≤ (9*x1^3*x3 + 3*x1^3*x4 + 9*x1^2*x2^2 - 21*x1^2*x2*x3 - 8*x1^2*x2*x4 - 9*x1^2*x3^2 + 24*x1^2*x3*x4 + 9*x1^2*x4^2 + 3*x1*x2^3 - 8*x1*x2^2*x3 + 24*x1*x2^2*x4 + 24*x1*x2*x3^2 - 46*x1*x2*x3*x4 - 21*x1*x2*x4^2 + 9*x1*x3^3 - 21*x1*x3^2*x4 - 8*x1*x3*x4^2 + 9*x2^3*x4 + 9*x2^2*x3^2 - 21*x2^2*x3*x4 - 9*x2^2*x4^2 + 3*x2*x3^3 - 8*x2*x3^2*x4 + 24*x2*x3*x4^2 + 9*x2*x4^3 + 9*x3^2*x4^2 + 3*x3*x4^3) := by
    rcases le_total x2 x1 with hcase1 | hcase1
    ·
      rcases le_total x3 x2 with hcase2 | hcase2
      ·
        rcases le_total x4 x3 with hcase3 | hcase3
        ·
          convert haux5 x4 x1 x2 x3 (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
        ·
          rcases le_total x4 x2 with hcase4 | hcase4
          ·
            convert haux1 x3 x4 x1 x2 (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          ·
            rcases le_total x4 x1 with hcase5 | hcase5
            ·
              convert haux4 x3 x4 x1 x2 (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              convert haux5 x3 x4 x1 x2 (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
      ·
        rcases le_total x3 x1 with hcase6 | hcase6
        ·
          rcases le_total x4 x2 with hcase7 | hcase7
          ·
            convert haux3 x4 x1 x2 x3 (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          ·
            rcases le_total x4 x3 with hcase8 | hcase8
            ·
              convert haux2 x2 x3 x4 x1 (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              rcases le_total x4 x1 with hcase9 | hcase9
              ·
                convert haux0 x2 x3 x4 x1 (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
              ·
                convert haux1 x2 x3 x4 x1 (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
        ·
          rcases le_total x4 x2 with hcase10 | hcase10
          ·
            convert haux2 x4 x1 x2 x3 (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          ·
            rcases le_total x4 x1 with hcase11 | hcase11
            ·
              convert haux3 x2 x3 x4 x1 (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              rcases le_total x4 x3 with hcase12 | hcase12
              ·
                convert haux5 x2 x3 x4 x1 (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
              ·
                convert haux4 x2 x3 x4 x1 (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
    ·
      rcases le_total x3 x1 with hcase13 | hcase13
      ·
        rcases le_total x4 x3 with hcase14 | hcase14
        ·
          convert haux4 x4 x1 x2 x3 (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
        ·
          rcases le_total x4 x1 with hcase15 | hcase15
          ·
            convert haux0 x3 x4 x1 x2 (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          ·
            rcases le_total x4 x2 with hcase16 | hcase16
            ·
              convert haux2 x3 x4 x1 x2 (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              convert haux3 x3 x4 x1 x2 (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
      ·
        rcases le_total x3 x2 with hcase17 | hcase17
        ·
          rcases le_total x4 x1 with hcase18 | hcase18
          ·
            convert haux1 x4 x1 x2 x3 (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          ·
            rcases le_total x4 x3 with hcase19 | hcase19
            ·
              convert haux5 x1 x2 x3 x4 (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              rcases le_total x4 x2 with hcase20 | hcase20
              ·
                convert haux3 x1 x2 x3 x4 (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
              ·
                convert haux2 x1 x2 x3 x4 (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
        ·
          rcases le_total x4 x1 with hcase21 | hcase21
          ·
            convert haux0 x4 x1 x2 x3 (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          ·
            rcases le_total x4 x2 with hcase22 | hcase22
            ·
              convert haux4 x1 x2 x3 x4 (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              rcases le_total x4 x3 with hcase23 | hcase23
              ·
                convert haux1 x1 x2 x3 x4 (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
              ·
                convert haux0 x1 x2 x3 x4 (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
  have hn : 0 ≤ (9*x1^3*x3 + 3*x1^3*x4 + 9*x1^2*x2^2 - 21*x1^2*x2*x3 - 8*x1^2*x2*x4 - 9*x1^2*x3^2 + 24*x1^2*x3*x4 + 9*x1^2*x4^2 + 3*x1*x2^3 - 8*x1*x2^2*x3 + 24*x1*x2^2*x4 + 24*x1*x2*x3^2 - 46*x1*x2*x3*x4 - 21*x1*x2*x4^2 + 9*x1*x3^3 - 21*x1*x3^2*x4 - 8*x1*x3*x4^2 + 9*x2^3*x4 + 9*x2^2*x3^2 - 21*x2^2*x3*x4 - 9*x2^2*x4^2 + 3*x2*x3^3 - 8*x2*x3^2*x4 + 24*x2*x3*x4^2 + 9*x2*x4^3 + 9*x3^2*x4^2 + 3*x3*x4^3) := by nlinarith only [hp]
  have hd : (0 : ℝ) < ((x1 + 3*x4)*(3*x1 + x2)*(3*x2 + x3)*(3*x3 + x4)) := by positivity
  have heqrat : ( (x1 / (3 * x2 + x3) + x2 / (3 * x3 + x4) + x3 / (3 * x4 + x1) + x4 / (3 * x1 + x2)) ) - ( 1  ) = (9*x1^3*x3 + 3*x1^3*x4 + 9*x1^2*x2^2 - 21*x1^2*x2*x3 - 8*x1^2*x2*x4 - 9*x1^2*x3^2 + 24*x1^2*x3*x4 + 9*x1^2*x4^2 + 3*x1*x2^3 - 8*x1*x2^2*x3 + 24*x1*x2^2*x4 + 24*x1*x2*x3^2 - 46*x1*x2*x3*x4 - 21*x1*x2*x4^2 + 9*x1*x3^3 - 21*x1*x3^2*x4 - 8*x1*x3*x4^2 + 9*x2^3*x4 + 9*x2^2*x3^2 - 21*x2^2*x3*x4 - 9*x2^2*x4^2 + 3*x2*x3^3 - 8*x2*x3^2*x4 + 24*x2*x3*x4^2 + 9*x2*x4^3 + 9*x3^2*x4^2 + 3*x3*x4^3) / ((x1 + 3*x4)*(3*x1 + x2)*(3*x2 + x3)*(3*x3 + x4)) := by
    field_simp (disch := positivity)
    <;> ring
  have hfrac := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hfrac]
example : (∀ (x1 x2 x3 x4 : ℝ) (hx1 : 0 < x1) (hx2 : 0 < x2) (hx3 : 0 < x3) (hx4 : 0 < x4), (x1 / (3 * x2 + x3) + x2 / (3 * x3 + x4) + x3 / (3 * x4 + x1) + x4 / (3 * x1 + x2)) ≥ 1) := @solution
#print axioms solution
