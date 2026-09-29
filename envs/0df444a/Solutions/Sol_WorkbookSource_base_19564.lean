-- Prove2me | solution 1 for WorkbookSource.base_19564
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T11:38:32.824038+00:00
-- url     : https://prove2.me/submissions/79312831-6765-45f2-b920-ea433c43a1c4

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
private lemma p2mIndependent0 (gap0 gap1 gap2 gap3 : ℝ) (hg0 : 0 ≤ gap0) (hg1 : 0 ≤ gap1) (hg2 : 0 ≤ gap2) (hg3 : 0 ≤ gap3) : 0 ≤ ((gap0)^3*(gap0 + gap1 + gap2) + (gap0)^3*(gap0 + gap1 + gap2 + gap3) + (gap0)^2*(gap0 + gap1)^2 - (gap0)^2*(gap0 + gap1)*(gap0 + gap1 + gap2) - 2*(gap0)^2*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3) + (gap0)^2*(gap0 + gap1 + gap2)^2 + 2*(gap0)^2*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3) + (gap0)^2*(gap0 + gap1 + gap2 + gap3)^2 + (gap0)*(gap0 + gap1)^3 - 2*(gap0)*(gap0 + gap1)^2*(gap0 + gap1 + gap2) + 2*(gap0)*(gap0 + gap1)^2*(gap0 + gap1 + gap2 + gap3) + 2*(gap0)*(gap0 + gap1)*(gap0 + gap1 + gap2)^2 - 10*(gap0)*(gap0 + gap1)*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3) - (gap0)*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3)^2 + (gap0)*(gap0 + gap1 + gap2)^3 - (gap0)*(gap0 + gap1 + gap2)^2*(gap0 + gap1 + gap2 + gap3) - 2*(gap0)*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3)^2 + (gap0 + gap1)^3*(gap0 + gap1 + gap2 + gap3) + (gap0 + gap1)^2*(gap0 + gap1 + gap2)^2 - (gap0 + gap1)^2*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3) + (gap0 + gap1)^2*(gap0 + gap1 + gap2 + gap3)^2 + (gap0 + gap1)*(gap0 + gap1 + gap2)^3 - 2*(gap0 + gap1)*(gap0 + gap1 + gap2)^2*(gap0 + gap1 + gap2 + gap3) + 2*(gap0 + gap1)*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3)^2 + (gap0 + gap1)*(gap0 + gap1 + gap2 + gap3)^3 + (gap0 + gap1 + gap2)^2*(gap0 + gap1 + gap2 + gap3)^2 + (gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3)^3) := by
  have hpos : 0 ≤ (8 : ℝ) * (gap0^2 * gap1^2) + (8 : ℝ) * (gap0^2 * gap1^1 * gap2^1) + (8 : ℝ) * (gap0^2 * gap1^1 * gap3^1) + (8 : ℝ) * (gap0^2 * gap2^2) + (8 : ℝ) * (gap0^2 * gap2^1 * gap3^1) + (8 : ℝ) * (gap0^2 * gap3^2) + (14 : ℝ) * (gap0^1 * gap1^3) + (27 : ℝ) * (gap0^1 * gap1^2 * gap2^1) + (21 : ℝ) * (gap0^1 * gap1^2 * gap3^1) + (23 : ℝ) * (gap0^1 * gap1^1 * gap2^2) + (30 : ℝ) * (gap0^1 * gap1^1 * gap2^1 * gap3^1) + (17 : ℝ) * (gap0^1 * gap1^1 * gap3^2) + (8 : ℝ) * (gap0^1 * gap2^3) + (15 : ℝ) * (gap0^1 * gap2^2 * gap3^1) + (11 : ℝ) * (gap0^1 * gap2^1 * gap3^2) + (2 : ℝ) * (gap0^1 * gap3^3) + (6 : ℝ) * (gap1^4) + (17 : ℝ) * (gap1^3 * gap2^1) + (12 : ℝ) * (gap1^3 * gap3^1) + (19 : ℝ) * (gap1^2 * gap2^2) + (26 : ℝ) * (gap1^2 * gap2^1 * gap3^1) + (10 : ℝ) * (gap1^2 * gap3^2) + (10 : ℝ) * (gap1^1 * gap2^3) + (20 : ℝ) * (gap1^1 * gap2^2 * gap3^1) + (13 : ℝ) * (gap1^1 * gap2^1 * gap3^2) + (2 : ℝ) * (gap1^1 * gap3^3) + (2 : ℝ) * (gap2^4) + (5 : ℝ) * (gap2^3 * gap3^1) + (4 : ℝ) * (gap2^2 * gap3^2) + (1 : ℝ) * (gap2^1 * gap3^3) := by positivity
  convert hpos using 1 <;> ring

private lemma p2mIndependent1 (gap0 gap1 gap2 gap3 : ℝ) (hg0 : 0 ≤ gap0) (hg1 : 0 ≤ gap1) (hg2 : 0 ≤ gap2) (hg3 : 0 ≤ gap3) : 0 ≤ ((gap0)^3*(gap0 + gap1 + gap2 + gap3) + (gap0)^3*(gap0 + gap1 + gap2) + (gap0)^2*(gap0 + gap1)^2 - (gap0)^2*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3) - 2*(gap0)^2*(gap0 + gap1)*(gap0 + gap1 + gap2) + (gap0)^2*(gap0 + gap1 + gap2 + gap3)^2 + 2*(gap0)^2*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1 + gap2) + (gap0)^2*(gap0 + gap1 + gap2)^2 + (gap0)*(gap0 + gap1)^3 - 2*(gap0)*(gap0 + gap1)^2*(gap0 + gap1 + gap2 + gap3) + 2*(gap0)*(gap0 + gap1)^2*(gap0 + gap1 + gap2) + 2*(gap0)*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3)^2 - 10*(gap0)*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1 + gap2) - (gap0)*(gap0 + gap1)*(gap0 + gap1 + gap2)^2 + (gap0)*(gap0 + gap1 + gap2 + gap3)^3 - (gap0)*(gap0 + gap1 + gap2 + gap3)^2*(gap0 + gap1 + gap2) - 2*(gap0)*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1 + gap2)^2 + (gap0 + gap1)^3*(gap0 + gap1 + gap2) + (gap0 + gap1)^2*(gap0 + gap1 + gap2 + gap3)^2 - (gap0 + gap1)^2*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1 + gap2) + (gap0 + gap1)^2*(gap0 + gap1 + gap2)^2 + (gap0 + gap1)*(gap0 + gap1 + gap2 + gap3)^3 - 2*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3)^2*(gap0 + gap1 + gap2) + 2*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1 + gap2)^2 + (gap0 + gap1)*(gap0 + gap1 + gap2)^3 + (gap0 + gap1 + gap2 + gap3)^2*(gap0 + gap1 + gap2)^2 + (gap0 + gap1 + gap2 + gap3)*(gap0 + gap1 + gap2)^3) := by
  have hpos : 0 ≤ (8 : ℝ) * (gap0^2 * gap1^2) + (8 : ℝ) * (gap0^2 * gap1^1 * gap2^1) + (8 : ℝ) * (gap0^2 * gap2^2) + (8 : ℝ) * (gap0^2 * gap2^1 * gap3^1) + (8 : ℝ) * (gap0^2 * gap3^2) + (14 : ℝ) * (gap0^1 * gap1^3) + (27 : ℝ) * (gap0^1 * gap1^2 * gap2^1) + (6 : ℝ) * (gap0^1 * gap1^2 * gap3^1) + (23 : ℝ) * (gap0^1 * gap1^1 * gap2^2) + (16 : ℝ) * (gap0^1 * gap1^1 * gap2^1 * gap3^1) + (10 : ℝ) * (gap0^1 * gap1^1 * gap3^2) + (8 : ℝ) * (gap0^1 * gap2^3) + (9 : ℝ) * (gap0^1 * gap2^2 * gap3^1) + (5 : ℝ) * (gap0^1 * gap2^1 * gap3^2) + (2 : ℝ) * (gap0^1 * gap3^3) + (6 : ℝ) * (gap1^4) + (17 : ℝ) * (gap1^3 * gap2^1) + (5 : ℝ) * (gap1^3 * gap3^1) + (19 : ℝ) * (gap1^2 * gap2^2) + (12 : ℝ) * (gap1^2 * gap2^1 * gap3^1) + (3 : ℝ) * (gap1^2 * gap3^2) + (10 : ℝ) * (gap1^1 * gap2^3) + (10 : ℝ) * (gap1^1 * gap2^2 * gap3^1) + (3 : ℝ) * (gap1^1 * gap2^1 * gap3^2) + (1 : ℝ) * (gap1^1 * gap3^3) + (2 : ℝ) * (gap2^4) + (3 : ℝ) * (gap2^3 * gap3^1) + (1 : ℝ) * (gap2^2 * gap3^2) := by positivity
  convert hpos using 1 <;> ring

private lemma p2mIndependent2 (gap0 gap1 gap2 gap3 : ℝ) (hg0 : 0 ≤ gap0) (hg1 : 0 ≤ gap1) (hg2 : 0 ≤ gap2) (hg3 : 0 ≤ gap3) : 0 ≤ ((gap0)^3*(gap0 + gap1) + (gap0)^3*(gap0 + gap1 + gap2 + gap3) + (gap0)^2*(gap0 + gap1 + gap2)^2 - (gap0)^2*(gap0 + gap1 + gap2)*(gap0 + gap1) - 2*(gap0)^2*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3) + (gap0)^2*(gap0 + gap1)^2 + 2*(gap0)^2*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3) + (gap0)^2*(gap0 + gap1 + gap2 + gap3)^2 + (gap0)*(gap0 + gap1 + gap2)^3 - 2*(gap0)*(gap0 + gap1 + gap2)^2*(gap0 + gap1) + 2*(gap0)*(gap0 + gap1 + gap2)^2*(gap0 + gap1 + gap2 + gap3) + 2*(gap0)*(gap0 + gap1 + gap2)*(gap0 + gap1)^2 - 10*(gap0)*(gap0 + gap1 + gap2)*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3) - (gap0)*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3)^2 + (gap0)*(gap0 + gap1)^3 - (gap0)*(gap0 + gap1)^2*(gap0 + gap1 + gap2 + gap3) - 2*(gap0)*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3)^2 + (gap0 + gap1 + gap2)^3*(gap0 + gap1 + gap2 + gap3) + (gap0 + gap1 + gap2)^2*(gap0 + gap1)^2 - (gap0 + gap1 + gap2)^2*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3) + (gap0 + gap1 + gap2)^2*(gap0 + gap1 + gap2 + gap3)^2 + (gap0 + gap1 + gap2)*(gap0 + gap1)^3 - 2*(gap0 + gap1 + gap2)*(gap0 + gap1)^2*(gap0 + gap1 + gap2 + gap3) + 2*(gap0 + gap1 + gap2)*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3)^2 + (gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3)^3 + (gap0 + gap1)^2*(gap0 + gap1 + gap2 + gap3)^2 + (gap0 + gap1)*(gap0 + gap1 + gap2 + gap3)^3) := by
  have hpos : 0 ≤ (8 : ℝ) * (gap0^2 * gap1^2) + (16 : ℝ) * (gap0^2 * gap1^1 * gap2^1) + (8 : ℝ) * (gap0^2 * gap1^1 * gap3^1) + (16 : ℝ) * (gap0^2 * gap2^2) + (16 : ℝ) * (gap0^2 * gap2^1 * gap3^1) + (8 : ℝ) * (gap0^2 * gap3^2) + (14 : ℝ) * (gap0^1 * gap1^3) + (36 : ℝ) * (gap0^1 * gap1^2 * gap2^1) + (21 : ℝ) * (gap0^1 * gap1^2 * gap3^1) + (40 : ℝ) * (gap0^1 * gap1^1 * gap2^2) + (46 : ℝ) * (gap0^1 * gap1^1 * gap2^1 * gap3^1) + (17 : ℝ) * (gap0^1 * gap1^1 * gap3^2) + (16 : ℝ) * (gap0^1 * gap2^3) + (24 : ℝ) * (gap0^1 * gap2^2 * gap3^1) + (12 : ℝ) * (gap0^1 * gap2^1 * gap3^2) + (2 : ℝ) * (gap0^1 * gap3^3) + (6 : ℝ) * (gap1^4) + (19 : ℝ) * (gap1^3 * gap2^1) + (12 : ℝ) * (gap1^3 * gap3^1) + (24 : ℝ) * (gap1^2 * gap2^2) + (30 : ℝ) * (gap1^2 * gap2^1 * gap3^1) + (10 : ℝ) * (gap1^2 * gap3^2) + (14 : ℝ) * (gap1^1 * gap2^3) + (24 : ℝ) * (gap1^1 * gap2^2 * gap3^1) + (13 : ℝ) * (gap1^1 * gap2^1 * gap3^2) + (2 : ℝ) * (gap1^1 * gap3^3) + (3 : ℝ) * (gap2^4) + (6 : ℝ) * (gap2^3 * gap3^1) + (4 : ℝ) * (gap2^2 * gap3^2) + (1 : ℝ) * (gap2^1 * gap3^3) := by positivity
  convert hpos using 1 <;> ring

private lemma p2mIndependent3 (gap0 gap1 gap2 gap3 : ℝ) (hg0 : 0 ≤ gap0) (hg1 : 0 ≤ gap1) (hg2 : 0 ≤ gap2) (hg3 : 0 ≤ gap3) : 0 ≤ ((gap0)^3*(gap0 + gap1) + (gap0)^3*(gap0 + gap1 + gap2) + (gap0)^2*(gap0 + gap1 + gap2 + gap3)^2 - (gap0)^2*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1) - 2*(gap0)^2*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1 + gap2) + (gap0)^2*(gap0 + gap1)^2 + 2*(gap0)^2*(gap0 + gap1)*(gap0 + gap1 + gap2) + (gap0)^2*(gap0 + gap1 + gap2)^2 + (gap0)*(gap0 + gap1 + gap2 + gap3)^3 - 2*(gap0)*(gap0 + gap1 + gap2 + gap3)^2*(gap0 + gap1) + 2*(gap0)*(gap0 + gap1 + gap2 + gap3)^2*(gap0 + gap1 + gap2) + 2*(gap0)*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1)^2 - 10*(gap0)*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1)*(gap0 + gap1 + gap2) - (gap0)*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1 + gap2)^2 + (gap0)*(gap0 + gap1)^3 - (gap0)*(gap0 + gap1)^2*(gap0 + gap1 + gap2) - 2*(gap0)*(gap0 + gap1)*(gap0 + gap1 + gap2)^2 + (gap0 + gap1 + gap2 + gap3)^3*(gap0 + gap1 + gap2) + (gap0 + gap1 + gap2 + gap3)^2*(gap0 + gap1)^2 - (gap0 + gap1 + gap2 + gap3)^2*(gap0 + gap1)*(gap0 + gap1 + gap2) + (gap0 + gap1 + gap2 + gap3)^2*(gap0 + gap1 + gap2)^2 + (gap0 + gap1 + gap2 + gap3)*(gap0 + gap1)^3 - 2*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1)^2*(gap0 + gap1 + gap2) + 2*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1)*(gap0 + gap1 + gap2)^2 + (gap0 + gap1 + gap2 + gap3)*(gap0 + gap1 + gap2)^3 + (gap0 + gap1)^2*(gap0 + gap1 + gap2)^2 + (gap0 + gap1)*(gap0 + gap1 + gap2)^3) := by
  have hpos : 0 ≤ (8 : ℝ) * (gap0^2 * gap1^2) + (16 : ℝ) * (gap0^2 * gap1^1 * gap2^1) + (8 : ℝ) * (gap0^2 * gap1^1 * gap3^1) + (16 : ℝ) * (gap0^2 * gap2^2) + (16 : ℝ) * (gap0^2 * gap2^1 * gap3^1) + (8 : ℝ) * (gap0^2 * gap3^2) + (14 : ℝ) * (gap0^1 * gap1^3) + (36 : ℝ) * (gap0^1 * gap1^2 * gap2^1) + (15 : ℝ) * (gap0^1 * gap1^2 * gap3^1) + (40 : ℝ) * (gap0^1 * gap1^1 * gap2^2) + (34 : ℝ) * (gap0^1 * gap1^1 * gap2^1 * gap3^1) + (11 : ℝ) * (gap0^1 * gap1^1 * gap3^2) + (16 : ℝ) * (gap0^1 * gap2^3) + (24 : ℝ) * (gap0^1 * gap2^2 * gap3^1) + (12 : ℝ) * (gap0^1 * gap2^1 * gap3^2) + (2 : ℝ) * (gap0^1 * gap3^3) + (6 : ℝ) * (gap1^4) + (19 : ℝ) * (gap1^3 * gap2^1) + (7 : ℝ) * (gap1^3 * gap3^1) + (24 : ℝ) * (gap1^2 * gap2^2) + (18 : ℝ) * (gap1^2 * gap2^1 * gap3^1) + (4 : ℝ) * (gap1^2 * gap3^2) + (14 : ℝ) * (gap1^1 * gap2^3) + (18 : ℝ) * (gap1^1 * gap2^2 * gap3^1) + (7 : ℝ) * (gap1^1 * gap2^1 * gap3^2) + (1 : ℝ) * (gap1^1 * gap3^3) + (3 : ℝ) * (gap2^4) + (6 : ℝ) * (gap2^3 * gap3^1) + (4 : ℝ) * (gap2^2 * gap3^2) + (1 : ℝ) * (gap2^1 * gap3^3) := by positivity
  convert hpos using 1 <;> ring

private lemma p2mIndependent4 (gap0 gap1 gap2 gap3 : ℝ) (hg0 : 0 ≤ gap0) (hg1 : 0 ≤ gap1) (hg2 : 0 ≤ gap2) (hg3 : 0 ≤ gap3) : 0 ≤ ((gap0)^3*(gap0 + gap1 + gap2 + gap3) + (gap0)^3*(gap0 + gap1) + (gap0)^2*(gap0 + gap1 + gap2)^2 - (gap0)^2*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3) - 2*(gap0)^2*(gap0 + gap1 + gap2)*(gap0 + gap1) + (gap0)^2*(gap0 + gap1 + gap2 + gap3)^2 + 2*(gap0)^2*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1) + (gap0)^2*(gap0 + gap1)^2 + (gap0)*(gap0 + gap1 + gap2)^3 - 2*(gap0)*(gap0 + gap1 + gap2)^2*(gap0 + gap1 + gap2 + gap3) + 2*(gap0)*(gap0 + gap1 + gap2)^2*(gap0 + gap1) + 2*(gap0)*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3)^2 - 10*(gap0)*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1) - (gap0)*(gap0 + gap1 + gap2)*(gap0 + gap1)^2 + (gap0)*(gap0 + gap1 + gap2 + gap3)^3 - (gap0)*(gap0 + gap1 + gap2 + gap3)^2*(gap0 + gap1) - 2*(gap0)*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1)^2 + (gap0 + gap1 + gap2)^3*(gap0 + gap1) + (gap0 + gap1 + gap2)^2*(gap0 + gap1 + gap2 + gap3)^2 - (gap0 + gap1 + gap2)^2*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1) + (gap0 + gap1 + gap2)^2*(gap0 + gap1)^2 + (gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3)^3 - 2*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3)^2*(gap0 + gap1) + 2*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1)^2 + (gap0 + gap1 + gap2)*(gap0 + gap1)^3 + (gap0 + gap1 + gap2 + gap3)^2*(gap0 + gap1)^2 + (gap0 + gap1 + gap2 + gap3)*(gap0 + gap1)^3) := by
  have hpos : 0 ≤ (8 : ℝ) * (gap0^2 * gap1^2) + (8 : ℝ) * (gap0^2 * gap1^1 * gap2^1) + (8 : ℝ) * (gap0^2 * gap2^2) + (8 : ℝ) * (gap0^2 * gap2^1 * gap3^1) + (8 : ℝ) * (gap0^2 * gap3^2) + (14 : ℝ) * (gap0^1 * gap1^3) + (21 : ℝ) * (gap0^1 * gap1^2 * gap2^1) + (6 : ℝ) * (gap0^1 * gap1^2 * gap3^1) + (17 : ℝ) * (gap0^1 * gap1^1 * gap2^2) + (16 : ℝ) * (gap0^1 * gap1^1 * gap2^1 * gap3^1) + (10 : ℝ) * (gap0^1 * gap1^1 * gap3^2) + (8 : ℝ) * (gap0^1 * gap2^3) + (15 : ℝ) * (gap0^1 * gap2^2 * gap3^1) + (11 : ℝ) * (gap0^1 * gap2^1 * gap3^2) + (2 : ℝ) * (gap0^1 * gap3^3) + (6 : ℝ) * (gap1^4) + (12 : ℝ) * (gap1^3 * gap2^1) + (5 : ℝ) * (gap1^3 * gap3^1) + (10 : ℝ) * (gap1^2 * gap2^2) + (9 : ℝ) * (gap1^2 * gap2^1 * gap3^1) + (3 : ℝ) * (gap1^2 * gap3^2) + (6 : ℝ) * (gap1^1 * gap2^3) + (10 : ℝ) * (gap1^1 * gap2^2 * gap3^1) + (6 : ℝ) * (gap1^1 * gap2^1 * gap3^2) + (1 : ℝ) * (gap1^1 * gap3^3) + (2 : ℝ) * (gap2^4) + (5 : ℝ) * (gap2^3 * gap3^1) + (4 : ℝ) * (gap2^2 * gap3^2) + (1 : ℝ) * (gap2^1 * gap3^3) := by positivity
  convert hpos using 1 <;> ring

private lemma p2mIndependent5 (gap0 gap1 gap2 gap3 : ℝ) (hg0 : 0 ≤ gap0) (hg1 : 0 ≤ gap1) (hg2 : 0 ≤ gap2) (hg3 : 0 ≤ gap3) : 0 ≤ ((gap0)^3*(gap0 + gap1 + gap2) + (gap0)^3*(gap0 + gap1) + (gap0)^2*(gap0 + gap1 + gap2 + gap3)^2 - (gap0)^2*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1 + gap2) - 2*(gap0)^2*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1) + (gap0)^2*(gap0 + gap1 + gap2)^2 + 2*(gap0)^2*(gap0 + gap1 + gap2)*(gap0 + gap1) + (gap0)^2*(gap0 + gap1)^2 + (gap0)*(gap0 + gap1 + gap2 + gap3)^3 - 2*(gap0)*(gap0 + gap1 + gap2 + gap3)^2*(gap0 + gap1 + gap2) + 2*(gap0)*(gap0 + gap1 + gap2 + gap3)^2*(gap0 + gap1) + 2*(gap0)*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1 + gap2)^2 - 10*(gap0)*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1 + gap2)*(gap0 + gap1) - (gap0)*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1)^2 + (gap0)*(gap0 + gap1 + gap2)^3 - (gap0)*(gap0 + gap1 + gap2)^2*(gap0 + gap1) - 2*(gap0)*(gap0 + gap1 + gap2)*(gap0 + gap1)^2 + (gap0 + gap1 + gap2 + gap3)^3*(gap0 + gap1) + (gap0 + gap1 + gap2 + gap3)^2*(gap0 + gap1 + gap2)^2 - (gap0 + gap1 + gap2 + gap3)^2*(gap0 + gap1 + gap2)*(gap0 + gap1) + (gap0 + gap1 + gap2 + gap3)^2*(gap0 + gap1)^2 + (gap0 + gap1 + gap2 + gap3)*(gap0 + gap1 + gap2)^3 - 2*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1 + gap2)^2*(gap0 + gap1) + 2*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1 + gap2)*(gap0 + gap1)^2 + (gap0 + gap1 + gap2 + gap3)*(gap0 + gap1)^3 + (gap0 + gap1 + gap2)^2*(gap0 + gap1)^2 + (gap0 + gap1 + gap2)*(gap0 + gap1)^3) := by
  have hpos : 0 ≤ (8 : ℝ) * (gap0^2 * gap1^2) + (8 : ℝ) * (gap0^2 * gap1^1 * gap2^1) + (8 : ℝ) * (gap0^2 * gap1^1 * gap3^1) + (8 : ℝ) * (gap0^2 * gap2^2) + (8 : ℝ) * (gap0^2 * gap2^1 * gap3^1) + (8 : ℝ) * (gap0^2 * gap3^2) + (14 : ℝ) * (gap0^1 * gap1^3) + (21 : ℝ) * (gap0^1 * gap1^2 * gap2^1) + (15 : ℝ) * (gap0^1 * gap1^2 * gap3^1) + (17 : ℝ) * (gap0^1 * gap1^1 * gap2^2) + (18 : ℝ) * (gap0^1 * gap1^1 * gap2^1 * gap3^1) + (11 : ℝ) * (gap0^1 * gap1^1 * gap3^2) + (8 : ℝ) * (gap0^1 * gap2^3) + (9 : ℝ) * (gap0^1 * gap2^2 * gap3^1) + (5 : ℝ) * (gap0^1 * gap2^1 * gap3^2) + (2 : ℝ) * (gap0^1 * gap3^3) + (6 : ℝ) * (gap1^4) + (12 : ℝ) * (gap1^3 * gap2^1) + (7 : ℝ) * (gap1^3 * gap3^1) + (10 : ℝ) * (gap1^2 * gap2^2) + (11 : ℝ) * (gap1^2 * gap2^1 * gap3^1) + (4 : ℝ) * (gap1^2 * gap3^2) + (6 : ℝ) * (gap1^1 * gap2^3) + (8 : ℝ) * (gap1^1 * gap2^2 * gap3^1) + (4 : ℝ) * (gap1^1 * gap2^1 * gap3^2) + (1 : ℝ) * (gap1^1 * gap3^3) + (2 : ℝ) * (gap2^4) + (3 : ℝ) * (gap2^3 * gap3^1) + (1 : ℝ) * (gap2^2 * gap3^2) := by positivity
  convert hpos using 1 <;> ring
theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : a / (2 * a + b + c) + b / (2 * b + c + d) + c / (2 * c + d + a) + d / (2 * d + a + b) ≤ 1  := by
  have haux0 (a b c d : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) (hord3 : c ≤ d) : 0 ≤ (a^3*c + a^3*d + a^2*b^2 - a^2*b*c - 2*a^2*b*d + a^2*c^2 + 2*a^2*c*d + a^2*d^2 + a*b^3 - 2*a*b^2*c + 2*a*b^2*d + 2*a*b*c^2 - 10*a*b*c*d - a*b*d^2 + a*c^3 - a*c^2*d - 2*a*c*d^2 + b^3*d + b^2*c^2 - b^2*c*d + b^2*d^2 + b*c^3 - 2*b*c^2*d + 2*b*c*d^2 + b*d^3 + c^2*d^2 + c*d^3) := by
    have hd1 : 0 ≤ b - a := by linarith only [hord1]
    have hd2 : 0 ≤ c - b := by linarith only [hord2]
    have hd3 : 0 ≤ d - c := by linarith only [hord3]
    have hi := p2mIndependent0 a (b - a) (c - b) (d - c) hlow hd1 hd2 hd3
    convert hi using 1 <;> ring
  have haux1 (a b c d : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ d) (hord3 : d ≤ c) : 0 ≤ (a^3*c + a^3*d + a^2*b^2 - a^2*b*c - 2*a^2*b*d + a^2*c^2 + 2*a^2*c*d + a^2*d^2 + a*b^3 - 2*a*b^2*c + 2*a*b^2*d + 2*a*b*c^2 - 10*a*b*c*d - a*b*d^2 + a*c^3 - a*c^2*d - 2*a*c*d^2 + b^3*d + b^2*c^2 - b^2*c*d + b^2*d^2 + b*c^3 - 2*b*c^2*d + 2*b*c*d^2 + b*d^3 + c^2*d^2 + c*d^3) := by
    have hd1 : 0 ≤ b - a := by linarith only [hord1]
    have hd2 : 0 ≤ d - b := by linarith only [hord2]
    have hd3 : 0 ≤ c - d := by linarith only [hord3]
    have hi := p2mIndependent1 a (b - a) (d - b) (c - d) hlow hd1 hd2 hd3
    convert hi using 1 <;> ring
  have haux2 (a b c d : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) (hord3 : b ≤ d) : 0 ≤ (a^3*c + a^3*d + a^2*b^2 - a^2*b*c - 2*a^2*b*d + a^2*c^2 + 2*a^2*c*d + a^2*d^2 + a*b^3 - 2*a*b^2*c + 2*a*b^2*d + 2*a*b*c^2 - 10*a*b*c*d - a*b*d^2 + a*c^3 - a*c^2*d - 2*a*c*d^2 + b^3*d + b^2*c^2 - b^2*c*d + b^2*d^2 + b*c^3 - 2*b*c^2*d + 2*b*c*d^2 + b*d^3 + c^2*d^2 + c*d^3) := by
    have hd1 : 0 ≤ c - a := by linarith only [hord1]
    have hd2 : 0 ≤ b - c := by linarith only [hord2]
    have hd3 : 0 ≤ d - b := by linarith only [hord3]
    have hi := p2mIndependent2 a (c - a) (b - c) (d - b) hlow hd1 hd2 hd3
    convert hi using 1 <;> ring
  have haux3 (a b c d : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ d) (hord3 : d ≤ b) : 0 ≤ (a^3*c + a^3*d + a^2*b^2 - a^2*b*c - 2*a^2*b*d + a^2*c^2 + 2*a^2*c*d + a^2*d^2 + a*b^3 - 2*a*b^2*c + 2*a*b^2*d + 2*a*b*c^2 - 10*a*b*c*d - a*b*d^2 + a*c^3 - a*c^2*d - 2*a*c*d^2 + b^3*d + b^2*c^2 - b^2*c*d + b^2*d^2 + b*c^3 - 2*b*c^2*d + 2*b*c*d^2 + b*d^3 + c^2*d^2 + c*d^3) := by
    have hd1 : 0 ≤ c - a := by linarith only [hord1]
    have hd2 : 0 ≤ d - c := by linarith only [hord2]
    have hd3 : 0 ≤ b - d := by linarith only [hord3]
    have hi := p2mIndependent3 a (c - a) (d - c) (b - d) hlow hd1 hd2 hd3
    convert hi using 1 <;> ring
  have haux4 (a b c d : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ d) (hord2 : d ≤ b) (hord3 : b ≤ c) : 0 ≤ (a^3*c + a^3*d + a^2*b^2 - a^2*b*c - 2*a^2*b*d + a^2*c^2 + 2*a^2*c*d + a^2*d^2 + a*b^3 - 2*a*b^2*c + 2*a*b^2*d + 2*a*b*c^2 - 10*a*b*c*d - a*b*d^2 + a*c^3 - a*c^2*d - 2*a*c*d^2 + b^3*d + b^2*c^2 - b^2*c*d + b^2*d^2 + b*c^3 - 2*b*c^2*d + 2*b*c*d^2 + b*d^3 + c^2*d^2 + c*d^3) := by
    have hd1 : 0 ≤ d - a := by linarith only [hord1]
    have hd2 : 0 ≤ b - d := by linarith only [hord2]
    have hd3 : 0 ≤ c - b := by linarith only [hord3]
    have hi := p2mIndependent4 a (d - a) (b - d) (c - b) hlow hd1 hd2 hd3
    convert hi using 1 <;> ring
  have haux5 (a b c d : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ d) (hord2 : d ≤ c) (hord3 : c ≤ b) : 0 ≤ (a^3*c + a^3*d + a^2*b^2 - a^2*b*c - 2*a^2*b*d + a^2*c^2 + 2*a^2*c*d + a^2*d^2 + a*b^3 - 2*a*b^2*c + 2*a*b^2*d + 2*a*b*c^2 - 10*a*b*c*d - a*b*d^2 + a*c^3 - a*c^2*d - 2*a*c*d^2 + b^3*d + b^2*c^2 - b^2*c*d + b^2*d^2 + b*c^3 - 2*b*c^2*d + 2*b*c*d^2 + b*d^3 + c^2*d^2 + c*d^3) := by
    have hd1 : 0 ≤ d - a := by linarith only [hord1]
    have hd2 : 0 ≤ c - d := by linarith only [hord2]
    have hd3 : 0 ≤ b - c := by linarith only [hord3]
    have hi := p2mIndependent5 a (d - a) (c - d) (b - c) hlow hd1 hd2 hd3
    convert hi using 1 <;> ring
  have hp : 0 ≤ (a^3*c + a^3*d + a^2*b^2 - a^2*b*c - 2*a^2*b*d + a^2*c^2 + 2*a^2*c*d + a^2*d^2 + a*b^3 - 2*a*b^2*c + 2*a*b^2*d + 2*a*b*c^2 - 10*a*b*c*d - a*b*d^2 + a*c^3 - a*c^2*d - 2*a*c*d^2 + b^3*d + b^2*c^2 - b^2*c*d + b^2*d^2 + b*c^3 - 2*b*c^2*d + 2*b*c*d^2 + b*d^3 + c^2*d^2 + c*d^3) := by
    rcases le_total b a with hcase1 | hcase1
    ·
      rcases le_total c b with hcase2 | hcase2
      ·
        rcases le_total d c with hcase3 | hcase3
        ·
          convert haux5 d a b c (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
        ·
          rcases le_total d b with hcase4 | hcase4
          ·
            convert haux1 c d a b (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          ·
            rcases le_total d a with hcase5 | hcase5
            ·
              convert haux4 c d a b (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              convert haux5 c d a b (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
      ·
        rcases le_total c a with hcase6 | hcase6
        ·
          rcases le_total d b with hcase7 | hcase7
          ·
            convert haux3 d a b c (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
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
              convert haux3 b c d a (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              rcases le_total d c with hcase12 | hcase12
              ·
                convert haux5 b c d a (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
              ·
                convert haux4 b c d a (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
    ·
      rcases le_total c a with hcase13 | hcase13
      ·
        rcases le_total d c with hcase14 | hcase14
        ·
          convert haux4 d a b c (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
        ·
          rcases le_total d a with hcase15 | hcase15
          ·
            convert haux0 c d a b (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          ·
            rcases le_total d b with hcase16 | hcase16
            ·
              convert haux2 c d a b (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              convert haux3 c d a b (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
      ·
        rcases le_total c b with hcase17 | hcase17
        ·
          rcases le_total d a with hcase18 | hcase18
          ·
            convert haux1 d a b c (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          ·
            rcases le_total d c with hcase19 | hcase19
            ·
              convert haux5 a b c d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              rcases le_total d b with hcase20 | hcase20
              ·
                convert haux3 a b c d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
              ·
                convert haux2 a b c d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
        ·
          rcases le_total d a with hcase21 | hcase21
          ·
            convert haux0 d a b c (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          ·
            rcases le_total d b with hcase22 | hcase22
            ·
              convert haux4 a b c d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              rcases le_total d c with hcase23 | hcase23
              ·
                convert haux1 a b c d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
              ·
                convert haux0 a b c d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
  have hn : 0 ≤ (a^3*c + a^3*d + a^2*b^2 - a^2*b*c - 2*a^2*b*d + a^2*c^2 + 2*a^2*c*d + a^2*d^2 + a*b^3 - 2*a*b^2*c + 2*a*b^2*d + 2*a*b*c^2 - 10*a*b*c*d - a*b*d^2 + a*c^3 - a*c^2*d - 2*a*c*d^2 + b^3*d + b^2*c^2 - b^2*c*d + b^2*d^2 + b*c^3 - 2*b*c^2*d + 2*b*c*d^2 + b*d^3 + c^2*d^2 + c*d^3) := by nlinarith only [hp]
  have hd : (0 : ℝ) < ((a + b + 2*d)*(a + 2*c + d)*(2*a + b + c)*(2*b + c + d)) := by positivity
  have heqrat : ( 1  ) - ( a / (2 * a + b + c) + b / (2 * b + c + d) + c / (2 * c + d + a) + d / (2 * d + a + b) ) = (a^3*c + a^3*d + a^2*b^2 - a^2*b*c - 2*a^2*b*d + a^2*c^2 + 2*a^2*c*d + a^2*d^2 + a*b^3 - 2*a*b^2*c + 2*a*b^2*d + 2*a*b*c^2 - 10*a*b*c*d - a*b*d^2 + a*c^3 - a*c^2*d - 2*a*c*d^2 + b^3*d + b^2*c^2 - b^2*c*d + b^2*d^2 + b*c^3 - 2*b*c^2*d + 2*b*c*d^2 + b*d^3 + c^2*d^2 + c*d^3) / ((a + b + 2*d)*(a + 2*c + d)*(2*a + b + c)*(2*b + c + d)) := by
    field_simp (disch := positivity)
    <;> ring
  have hfrac := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hfrac]
example : (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d), a / (2 * a + b + c) + b / (2 * b + c + d) + c / (2 * c + d + a) + d / (2 * d + a + b) ≤ 1) := @solution
#print axioms solution
