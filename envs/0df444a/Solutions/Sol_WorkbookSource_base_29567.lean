-- Prove2me | solution 1 for WorkbookSource.base_29567
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T11:34:14.560309+00:00
-- url     : https://prove2.me/submissions/a098935b-06cb-4be1-9468-1ad5a7c3fc4f

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
private lemma p2mIndependent0 (gap0 gap1 gap2 gap3 : ℝ) (hg0 : 0 ≤ gap0) (hg1 : 0 ≤ gap1) (hg2 : 0 ≤ gap2) (hg3 : 0 ≤ gap3) : 0 ≤ (2*(gap0)^5 + 5*(gap0)^4*(gap0 + gap1) + 4*(gap0)^4*(gap0 + gap1 + gap2) + 5*(gap0)^4*(gap0 + gap1 + gap2 + gap3) + 2*(gap0)^3*(gap0 + gap1)^2 + 2*(gap0)^3*(gap0 + gap1)*(gap0 + gap1 + gap2) + 10*(gap0)^3*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3) - 6*(gap0)^3*(gap0 + gap1 + gap2)^2 + 2*(gap0)^3*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3) + 2*(gap0)^3*(gap0 + gap1 + gap2 + gap3)^2 + 2*(gap0)^2*(gap0 + gap1)^3 - 14*(gap0)^2*(gap0 + gap1)*(gap0 + gap1 + gap2)^2 - 14*(gap0)^2*(gap0 + gap1)*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3) - 6*(gap0)^2*(gap0 + gap1 + gap2)^3 - 14*(gap0)^2*(gap0 + gap1 + gap2)^2*(gap0 + gap1 + gap2 + gap3) + 2*(gap0)^2*(gap0 + gap1 + gap2 + gap3)^3 + 5*(gap0)*(gap0 + gap1)^4 + 10*(gap0)*(gap0 + gap1)^3*(gap0 + gap1 + gap2) + 2*(gap0)*(gap0 + gap1)^3*(gap0 + gap1 + gap2 + gap3) - 14*(gap0)*(gap0 + gap1)^2*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3) - 14*(gap0)*(gap0 + gap1)^2*(gap0 + gap1 + gap2 + gap3)^2 + 2*(gap0)*(gap0 + gap1)*(gap0 + gap1 + gap2)^3 - 14*(gap0)*(gap0 + gap1)*(gap0 + gap1 + gap2)^2*(gap0 + gap1 + gap2 + gap3) - 14*(gap0)*(gap0 + gap1)*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3)^2 + 2*(gap0)*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3)^3 + 4*(gap0)*(gap0 + gap1 + gap2)^4 + 2*(gap0)*(gap0 + gap1 + gap2)^3*(gap0 + gap1 + gap2 + gap3) + 10*(gap0)*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3)^3 + 5*(gap0)*(gap0 + gap1 + gap2 + gap3)^4 + 2*(gap0 + gap1)^5 + 5*(gap0 + gap1)^4*(gap0 + gap1 + gap2) + 4*(gap0 + gap1)^4*(gap0 + gap1 + gap2 + gap3) + 2*(gap0 + gap1)^3*(gap0 + gap1 + gap2)^2 + 2*(gap0 + gap1)^3*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3) - 6*(gap0 + gap1)^3*(gap0 + gap1 + gap2 + gap3)^2 + 2*(gap0 + gap1)^2*(gap0 + gap1 + gap2)^3 - 14*(gap0 + gap1)^2*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3)^2 - 6*(gap0 + gap1)^2*(gap0 + gap1 + gap2 + gap3)^3 + 5*(gap0 + gap1)*(gap0 + gap1 + gap2)^4 + 10*(gap0 + gap1)*(gap0 + gap1 + gap2)^3*(gap0 + gap1 + gap2 + gap3) + 2*(gap0 + gap1)*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3)^3 + 4*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3)^4 + 2*(gap0 + gap1 + gap2)^5 + 5*(gap0 + gap1 + gap2)^4*(gap0 + gap1 + gap2 + gap3) + 2*(gap0 + gap1 + gap2)^3*(gap0 + gap1 + gap2 + gap3)^2 + 2*(gap0 + gap1 + gap2)^2*(gap0 + gap1 + gap2 + gap3)^3 + 5*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3)^4 + 2*(gap0 + gap1 + gap2 + gap3)^5) := by
  have hpos : 0 ≤ (96 : ℝ) * (gap0^3 * gap1^2) + (192 : ℝ) * (gap0^3 * gap1^1 * gap2^1) + (192 : ℝ) * (gap0^3 * gap2^2) + (192 : ℝ) * (gap0^3 * gap2^1 * gap3^1) + (96 : ℝ) * (gap0^3 * gap3^2) + (200 : ℝ) * (gap0^2 * gap1^3) + (544 : ℝ) * (gap0^2 * gap1^2 * gap2^1) + (56 : ℝ) * (gap0^2 * gap1^2 * gap3^1) + (720 : ℝ) * (gap0^2 * gap1^1 * gap2^2) + (576 : ℝ) * (gap0^2 * gap1^1 * gap2^1 * gap3^1) + (232 : ℝ) * (gap0^2 * gap1^1 * gap3^2) + (288 : ℝ) * (gap0^2 * gap2^3) + (432 : ℝ) * (gap0^2 * gap2^2 * gap3^1) + (320 : ℝ) * (gap0^2 * gap2^1 * gap3^2) + (88 : ℝ) * (gap0^2 * gap3^3) + (136 : ℝ) * (gap0^1 * gap1^4) + (468 : ℝ) * (gap0^1 * gap1^3 * gap2^1) + (76 : ℝ) * (gap0^1 * gap1^3 * gap3^1) + (776 : ℝ) * (gap0^1 * gap1^2 * gap2^2) + (564 : ℝ) * (gap0^1 * gap1^2 * gap2^1 * gap3^1) + (188 : ℝ) * (gap0^1 * gap1^2 * gap3^2) + (552 : ℝ) * (gap0^1 * gap1^1 * gap2^3) + (760 : ℝ) * (gap0^1 * gap1^1 * gap2^2 * gap3^1) + (516 : ℝ) * (gap0^1 * gap1^1 * gap2^1 * gap3^2) + (140 : ℝ) * (gap0^1 * gap1^1 * gap3^3) + (132 : ℝ) * (gap0^1 * gap2^4) + (264 : ℝ) * (gap0^1 * gap2^3 * gap3^1) + (264 : ℝ) * (gap0^1 * gap2^2 * gap3^2) + (132 : ℝ) * (gap0^1 * gap2^1 * gap3^3) + (24 : ℝ) * (gap0^1 * gap3^4) + (30 : ℝ) * (gap1^5) + (125 : ℝ) * (gap1^4 * gap2^1) + (25 : ℝ) * (gap1^4 * gap3^1) + (250 : ℝ) * (gap1^3 * gap2^2) + (174 : ℝ) * (gap1^3 * gap2^1 * gap3^1) + (50 : ℝ) * (gap1^3 * gap3^2) + (246 : ℝ) * (gap1^2 * gap2^3) + (320 : ℝ) * (gap1^2 * gap2^2 * gap3^1) + (202 : ℝ) * (gap1^2 * gap2^1 * gap3^2) + (54 : ℝ) * (gap1^2 * gap3^3) + (111 : ℝ) * (gap1^1 * gap2^4) + (212 : ℝ) * (gap1^1 * gap2^3 * gap3^1) + (204 : ℝ) * (gap1^1 * gap2^2 * gap3^2) + (102 : ℝ) * (gap1^1 * gap2^1 * gap3^3) + (19 : ℝ) * (gap1^1 * gap3^4) + (18 : ℝ) * (gap2^5) + (45 : ℝ) * (gap2^4 * gap3^1) + (58 : ℝ) * (gap2^3 * gap3^2) + (42 : ℝ) * (gap2^2 * gap3^3) + (15 : ℝ) * (gap2^1 * gap3^4) + (2 : ℝ) * (gap3^5) := by positivity
  convert hpos using 1 <;> ring

private lemma p2mIndependent1 (gap0 gap1 gap2 gap3 : ℝ) (hg0 : 0 ≤ gap0) (hg1 : 0 ≤ gap1) (hg2 : 0 ≤ gap2) (hg3 : 0 ≤ gap3) : 0 ≤ (2*(gap0)^5 + 5*(gap0)^4*(gap0 + gap1) + 4*(gap0)^4*(gap0 + gap1 + gap2 + gap3) + 5*(gap0)^4*(gap0 + gap1 + gap2) + 2*(gap0)^3*(gap0 + gap1)^2 + 2*(gap0)^3*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3) + 10*(gap0)^3*(gap0 + gap1)*(gap0 + gap1 + gap2) - 6*(gap0)^3*(gap0 + gap1 + gap2 + gap3)^2 + 2*(gap0)^3*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1 + gap2) + 2*(gap0)^3*(gap0 + gap1 + gap2)^2 + 2*(gap0)^2*(gap0 + gap1)^3 - 14*(gap0)^2*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3)^2 - 14*(gap0)^2*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1 + gap2) - 6*(gap0)^2*(gap0 + gap1 + gap2 + gap3)^3 - 14*(gap0)^2*(gap0 + gap1 + gap2 + gap3)^2*(gap0 + gap1 + gap2) + 2*(gap0)^2*(gap0 + gap1 + gap2)^3 + 5*(gap0)*(gap0 + gap1)^4 + 10*(gap0)*(gap0 + gap1)^3*(gap0 + gap1 + gap2 + gap3) + 2*(gap0)*(gap0 + gap1)^3*(gap0 + gap1 + gap2) - 14*(gap0)*(gap0 + gap1)^2*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1 + gap2) - 14*(gap0)*(gap0 + gap1)^2*(gap0 + gap1 + gap2)^2 + 2*(gap0)*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3)^3 - 14*(gap0)*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3)^2*(gap0 + gap1 + gap2) - 14*(gap0)*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1 + gap2)^2 + 2*(gap0)*(gap0 + gap1)*(gap0 + gap1 + gap2)^3 + 4*(gap0)*(gap0 + gap1 + gap2 + gap3)^4 + 2*(gap0)*(gap0 + gap1 + gap2 + gap3)^3*(gap0 + gap1 + gap2) + 10*(gap0)*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1 + gap2)^3 + 5*(gap0)*(gap0 + gap1 + gap2)^4 + 2*(gap0 + gap1)^5 + 5*(gap0 + gap1)^4*(gap0 + gap1 + gap2 + gap3) + 4*(gap0 + gap1)^4*(gap0 + gap1 + gap2) + 2*(gap0 + gap1)^3*(gap0 + gap1 + gap2 + gap3)^2 + 2*(gap0 + gap1)^3*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1 + gap2) - 6*(gap0 + gap1)^3*(gap0 + gap1 + gap2)^2 + 2*(gap0 + gap1)^2*(gap0 + gap1 + gap2 + gap3)^3 - 14*(gap0 + gap1)^2*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1 + gap2)^2 - 6*(gap0 + gap1)^2*(gap0 + gap1 + gap2)^3 + 5*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3)^4 + 10*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3)^3*(gap0 + gap1 + gap2) + 2*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1 + gap2)^3 + 4*(gap0 + gap1)*(gap0 + gap1 + gap2)^4 + 2*(gap0 + gap1 + gap2 + gap3)^5 + 5*(gap0 + gap1 + gap2 + gap3)^4*(gap0 + gap1 + gap2) + 2*(gap0 + gap1 + gap2 + gap3)^3*(gap0 + gap1 + gap2)^2 + 2*(gap0 + gap1 + gap2 + gap3)^2*(gap0 + gap1 + gap2)^3 + 5*(gap0 + gap1 + gap2 + gap3)*(gap0 + gap1 + gap2)^4 + 2*(gap0 + gap1 + gap2)^5) := by
  have hpos : 0 ≤ (96 : ℝ) * (gap0^3 * gap1^2) + (192 : ℝ) * (gap0^3 * gap1^1 * gap2^1) + (192 : ℝ) * (gap0^3 * gap1^1 * gap3^1) + (192 : ℝ) * (gap0^3 * gap2^2) + (192 : ℝ) * (gap0^3 * gap2^1 * gap3^1) + (96 : ℝ) * (gap0^3 * gap3^2) + (200 : ℝ) * (gap0^2 * gap1^3) + (544 : ℝ) * (gap0^2 * gap1^2 * gap2^1) + (488 : ℝ) * (gap0^2 * gap1^2 * gap3^1) + (720 : ℝ) * (gap0^2 * gap1^1 * gap2^2) + (864 : ℝ) * (gap0^2 * gap1^1 * gap2^1 * gap3^1) + (376 : ℝ) * (gap0^2 * gap1^1 * gap3^2) + (288 : ℝ) * (gap0^2 * gap2^3) + (432 : ℝ) * (gap0^2 * gap2^2 * gap3^1) + (320 : ℝ) * (gap0^2 * gap2^1 * gap3^2) + (88 : ℝ) * (gap0^2 * gap3^3) + (136 : ℝ) * (gap0^1 * gap1^4) + (468 : ℝ) * (gap0^1 * gap1^3 * gap2^1) + (392 : ℝ) * (gap0^1 * gap1^3 * gap3^1) + (776 : ℝ) * (gap0^1 * gap1^2 * gap2^2) + (988 : ℝ) * (gap0^1 * gap1^2 * gap2^1 * gap3^1) + (400 : ℝ) * (gap0^1 * gap1^2 * gap3^2) + (552 : ℝ) * (gap0^1 * gap1^1 * gap2^3) + (896 : ℝ) * (gap0^1 * gap1^1 * gap2^2 * gap3^1) + (652 : ℝ) * (gap0^1 * gap1^1 * gap2^1 * gap3^2) + (168 : ℝ) * (gap0^1 * gap1^1 * gap3^3) + (132 : ℝ) * (gap0^1 * gap2^4) + (264 : ℝ) * (gap0^1 * gap2^3 * gap3^1) + (264 : ℝ) * (gap0^1 * gap2^2 * gap3^2) + (132 : ℝ) * (gap0^1 * gap2^1 * gap3^3) + (24 : ℝ) * (gap0^1 * gap3^4) + (30 : ℝ) * (gap1^5) + (125 : ℝ) * (gap1^4 * gap2^1) + (100 : ℝ) * (gap1^4 * gap3^1) + (250 : ℝ) * (gap1^3 * gap2^2) + (326 : ℝ) * (gap1^3 * gap2^1 * gap3^1) + (126 : ℝ) * (gap1^3 * gap3^2) + (246 : ℝ) * (gap1^2 * gap2^3) + (418 : ℝ) * (gap1^2 * gap2^2 * gap3^1) + (300 : ℝ) * (gap1^2 * gap2^1 * gap3^2) + (74 : ℝ) * (gap1^2 * gap3^3) + (111 : ℝ) * (gap1^1 * gap2^4) + (232 : ℝ) * (gap1^1 * gap2^3 * gap3^1) + (234 : ℝ) * (gap1^1 * gap2^2 * gap3^2) + (114 : ℝ) * (gap1^1 * gap2^1 * gap3^3) + (20 : ℝ) * (gap1^1 * gap3^4) + (18 : ℝ) * (gap2^5) + (45 : ℝ) * (gap2^4 * gap3^1) + (58 : ℝ) * (gap2^3 * gap3^2) + (42 : ℝ) * (gap2^2 * gap3^3) + (15 : ℝ) * (gap2^1 * gap3^4) + (2 : ℝ) * (gap3^5) := by positivity
  convert hpos using 1 <;> ring

private lemma p2mIndependent2 (gap0 gap1 gap2 gap3 : ℝ) (hg0 : 0 ≤ gap0) (hg1 : 0 ≤ gap1) (hg2 : 0 ≤ gap2) (hg3 : 0 ≤ gap3) : 0 ≤ (2*(gap0)^5 + 5*(gap0)^4*(gap0 + gap1 + gap2) + 4*(gap0)^4*(gap0 + gap1) + 5*(gap0)^4*(gap0 + gap1 + gap2 + gap3) + 2*(gap0)^3*(gap0 + gap1 + gap2)^2 + 2*(gap0)^3*(gap0 + gap1 + gap2)*(gap0 + gap1) + 10*(gap0)^3*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3) - 6*(gap0)^3*(gap0 + gap1)^2 + 2*(gap0)^3*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3) + 2*(gap0)^3*(gap0 + gap1 + gap2 + gap3)^2 + 2*(gap0)^2*(gap0 + gap1 + gap2)^3 - 14*(gap0)^2*(gap0 + gap1 + gap2)*(gap0 + gap1)^2 - 14*(gap0)^2*(gap0 + gap1 + gap2)*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3) - 6*(gap0)^2*(gap0 + gap1)^3 - 14*(gap0)^2*(gap0 + gap1)^2*(gap0 + gap1 + gap2 + gap3) + 2*(gap0)^2*(gap0 + gap1 + gap2 + gap3)^3 + 5*(gap0)*(gap0 + gap1 + gap2)^4 + 10*(gap0)*(gap0 + gap1 + gap2)^3*(gap0 + gap1) + 2*(gap0)*(gap0 + gap1 + gap2)^3*(gap0 + gap1 + gap2 + gap3) - 14*(gap0)*(gap0 + gap1 + gap2)^2*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3) - 14*(gap0)*(gap0 + gap1 + gap2)^2*(gap0 + gap1 + gap2 + gap3)^2 + 2*(gap0)*(gap0 + gap1 + gap2)*(gap0 + gap1)^3 - 14*(gap0)*(gap0 + gap1 + gap2)*(gap0 + gap1)^2*(gap0 + gap1 + gap2 + gap3) - 14*(gap0)*(gap0 + gap1 + gap2)*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3)^2 + 2*(gap0)*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3)^3 + 4*(gap0)*(gap0 + gap1)^4 + 2*(gap0)*(gap0 + gap1)^3*(gap0 + gap1 + gap2 + gap3) + 10*(gap0)*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3)^3 + 5*(gap0)*(gap0 + gap1 + gap2 + gap3)^4 + 2*(gap0 + gap1 + gap2)^5 + 5*(gap0 + gap1 + gap2)^4*(gap0 + gap1) + 4*(gap0 + gap1 + gap2)^4*(gap0 + gap1 + gap2 + gap3) + 2*(gap0 + gap1 + gap2)^3*(gap0 + gap1)^2 + 2*(gap0 + gap1 + gap2)^3*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3) - 6*(gap0 + gap1 + gap2)^3*(gap0 + gap1 + gap2 + gap3)^2 + 2*(gap0 + gap1 + gap2)^2*(gap0 + gap1)^3 - 14*(gap0 + gap1 + gap2)^2*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3)^2 - 6*(gap0 + gap1 + gap2)^2*(gap0 + gap1 + gap2 + gap3)^3 + 5*(gap0 + gap1 + gap2)*(gap0 + gap1)^4 + 10*(gap0 + gap1 + gap2)*(gap0 + gap1)^3*(gap0 + gap1 + gap2 + gap3) + 2*(gap0 + gap1 + gap2)*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3)^3 + 4*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3)^4 + 2*(gap0 + gap1)^5 + 5*(gap0 + gap1)^4*(gap0 + gap1 + gap2 + gap3) + 2*(gap0 + gap1)^3*(gap0 + gap1 + gap2 + gap3)^2 + 2*(gap0 + gap1)^2*(gap0 + gap1 + gap2 + gap3)^3 + 5*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3)^4 + 2*(gap0 + gap1 + gap2 + gap3)^5) := by
  have hpos : 0 ≤ (96 : ℝ) * (gap0^3 * gap1^2) + (96 : ℝ) * (gap0^3 * gap3^2) + (200 : ℝ) * (gap0^2 * gap1^3) + (112 : ℝ) * (gap0^2 * gap1^2 * gap2^1) + (56 : ℝ) * (gap0^2 * gap1^2 * gap3^1) + (232 : ℝ) * (gap0^2 * gap1^1 * gap3^2) + (176 : ℝ) * (gap0^2 * gap2^1 * gap3^2) + (88 : ℝ) * (gap0^2 * gap3^3) + (136 : ℝ) * (gap0^1 * gap1^4) + (152 : ℝ) * (gap0^1 * gap1^3 * gap2^1) + (76 : ℝ) * (gap0^1 * gap1^3 * gap3^1) + (40 : ℝ) * (gap0^1 * gap1^2 * gap2^2) + (40 : ℝ) * (gap0^1 * gap1^2 * gap2^1 * gap3^1) + (188 : ℝ) * (gap0^1 * gap1^2 * gap3^2) + (280 : ℝ) * (gap0^1 * gap1^1 * gap2^1 * gap3^2) + (140 : ℝ) * (gap0^1 * gap1^1 * gap3^3) + (104 : ℝ) * (gap0^1 * gap2^2 * gap3^2) + (104 : ℝ) * (gap0^1 * gap2^1 * gap3^3) + (24 : ℝ) * (gap0^1 * gap3^4) + (30 : ℝ) * (gap1^5) + (50 : ℝ) * (gap1^4 * gap2^1) + (25 : ℝ) * (gap1^4 * gap3^1) + (26 : ℝ) * (gap1^3 * gap2^2) + (26 : ℝ) * (gap1^3 * gap2^1 * gap3^1) + (50 : ℝ) * (gap1^3 * gap3^2) + (4 : ℝ) * (gap1^2 * gap2^3) + (6 : ℝ) * (gap1^2 * gap2^2 * gap3^1) + (110 : ℝ) * (gap1^2 * gap2^1 * gap3^2) + (54 : ℝ) * (gap1^2 * gap3^3) + (82 : ℝ) * (gap1^1 * gap2^2 * gap3^2) + (82 : ℝ) * (gap1^1 * gap2^1 * gap3^3) + (19 : ℝ) * (gap1^1 * gap3^4) + (20 : ℝ) * (gap2^3 * gap3^2) + (30 : ℝ) * (gap2^2 * gap3^3) + (14 : ℝ) * (gap2^1 * gap3^4) + (2 : ℝ) * (gap3^5) := by positivity
  convert hpos using 1 <;> ring
theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a^2 - b * d)/(b + d + 2 * c) + (b^2 - c * a)/(c + a + 2 * d) + (c^2 - d * b)/(d + b + 2 * a) + (d^2 - a * c)/(a + c + 2 * b) ≥ 0  := by
  have haux0 (a b c d : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) (hord3 : c ≤ d) : 0 ≤ (2*a^5 + 5*a^4*b + 4*a^4*c + 5*a^4*d + 2*a^3*b^2 + 2*a^3*b*c + 10*a^3*b*d - 6*a^3*c^2 + 2*a^3*c*d + 2*a^3*d^2 + 2*a^2*b^3 - 14*a^2*b*c^2 - 14*a^2*b*c*d - 6*a^2*c^3 - 14*a^2*c^2*d + 2*a^2*d^3 + 5*a*b^4 + 10*a*b^3*c + 2*a*b^3*d - 14*a*b^2*c*d - 14*a*b^2*d^2 + 2*a*b*c^3 - 14*a*b*c^2*d - 14*a*b*c*d^2 + 2*a*b*d^3 + 4*a*c^4 + 2*a*c^3*d + 10*a*c*d^3 + 5*a*d^4 + 2*b^5 + 5*b^4*c + 4*b^4*d + 2*b^3*c^2 + 2*b^3*c*d - 6*b^3*d^2 + 2*b^2*c^3 - 14*b^2*c*d^2 - 6*b^2*d^3 + 5*b*c^4 + 10*b*c^3*d + 2*b*c*d^3 + 4*b*d^4 + 2*c^5 + 5*c^4*d + 2*c^3*d^2 + 2*c^2*d^3 + 5*c*d^4 + 2*d^5) := by
    have hd1 : 0 ≤ b - a := by linarith only [hord1]
    have hd2 : 0 ≤ c - b := by linarith only [hord2]
    have hd3 : 0 ≤ d - c := by linarith only [hord3]
    have hi := p2mIndependent0 a (b - a) (c - b) (d - c) hlow hd1 hd2 hd3
    convert hi using 1 <;> ring
  have haux1 (a b c d : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ d) (hord3 : d ≤ c) : 0 ≤ (2*a^5 + 5*a^4*b + 4*a^4*c + 5*a^4*d + 2*a^3*b^2 + 2*a^3*b*c + 10*a^3*b*d - 6*a^3*c^2 + 2*a^3*c*d + 2*a^3*d^2 + 2*a^2*b^3 - 14*a^2*b*c^2 - 14*a^2*b*c*d - 6*a^2*c^3 - 14*a^2*c^2*d + 2*a^2*d^3 + 5*a*b^4 + 10*a*b^3*c + 2*a*b^3*d - 14*a*b^2*c*d - 14*a*b^2*d^2 + 2*a*b*c^3 - 14*a*b*c^2*d - 14*a*b*c*d^2 + 2*a*b*d^3 + 4*a*c^4 + 2*a*c^3*d + 10*a*c*d^3 + 5*a*d^4 + 2*b^5 + 5*b^4*c + 4*b^4*d + 2*b^3*c^2 + 2*b^3*c*d - 6*b^3*d^2 + 2*b^2*c^3 - 14*b^2*c*d^2 - 6*b^2*d^3 + 5*b*c^4 + 10*b*c^3*d + 2*b*c*d^3 + 4*b*d^4 + 2*c^5 + 5*c^4*d + 2*c^3*d^2 + 2*c^2*d^3 + 5*c*d^4 + 2*d^5) := by
    have hd1 : 0 ≤ b - a := by linarith only [hord1]
    have hd2 : 0 ≤ d - b := by linarith only [hord2]
    have hd3 : 0 ≤ c - d := by linarith only [hord3]
    have hi := p2mIndependent1 a (b - a) (d - b) (c - d) hlow hd1 hd2 hd3
    convert hi using 1 <;> ring
  have haux2 (a b c d : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) (hord3 : b ≤ d) : 0 ≤ (2*a^5 + 5*a^4*b + 4*a^4*c + 5*a^4*d + 2*a^3*b^2 + 2*a^3*b*c + 10*a^3*b*d - 6*a^3*c^2 + 2*a^3*c*d + 2*a^3*d^2 + 2*a^2*b^3 - 14*a^2*b*c^2 - 14*a^2*b*c*d - 6*a^2*c^3 - 14*a^2*c^2*d + 2*a^2*d^3 + 5*a*b^4 + 10*a*b^3*c + 2*a*b^3*d - 14*a*b^2*c*d - 14*a*b^2*d^2 + 2*a*b*c^3 - 14*a*b*c^2*d - 14*a*b*c*d^2 + 2*a*b*d^3 + 4*a*c^4 + 2*a*c^3*d + 10*a*c*d^3 + 5*a*d^4 + 2*b^5 + 5*b^4*c + 4*b^4*d + 2*b^3*c^2 + 2*b^3*c*d - 6*b^3*d^2 + 2*b^2*c^3 - 14*b^2*c*d^2 - 6*b^2*d^3 + 5*b*c^4 + 10*b*c^3*d + 2*b*c*d^3 + 4*b*d^4 + 2*c^5 + 5*c^4*d + 2*c^3*d^2 + 2*c^2*d^3 + 5*c*d^4 + 2*d^5) := by
    have hd1 : 0 ≤ c - a := by linarith only [hord1]
    have hd2 : 0 ≤ b - c := by linarith only [hord2]
    have hd3 : 0 ≤ d - b := by linarith only [hord3]
    have hi := p2mIndependent2 a (c - a) (b - c) (d - b) hlow hd1 hd2 hd3
    convert hi using 1 <;> ring
  have hp : 0 ≤ (2*a^5 + 5*a^4*b + 4*a^4*c + 5*a^4*d + 2*a^3*b^2 + 2*a^3*b*c + 10*a^3*b*d - 6*a^3*c^2 + 2*a^3*c*d + 2*a^3*d^2 + 2*a^2*b^3 - 14*a^2*b*c^2 - 14*a^2*b*c*d - 6*a^2*c^3 - 14*a^2*c^2*d + 2*a^2*d^3 + 5*a*b^4 + 10*a*b^3*c + 2*a*b^3*d - 14*a*b^2*c*d - 14*a*b^2*d^2 + 2*a*b*c^3 - 14*a*b*c^2*d - 14*a*b*c*d^2 + 2*a*b*d^3 + 4*a*c^4 + 2*a*c^3*d + 10*a*c*d^3 + 5*a*d^4 + 2*b^5 + 5*b^4*c + 4*b^4*d + 2*b^3*c^2 + 2*b^3*c*d - 6*b^3*d^2 + 2*b^2*c^3 - 14*b^2*c*d^2 - 6*b^2*d^3 + 5*b*c^4 + 10*b*c^3*d + 2*b*c*d^3 + 4*b*d^4 + 2*c^5 + 5*c^4*d + 2*c^3*d^2 + 2*c^2*d^3 + 5*c*d^4 + 2*d^5) := by
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
  have hn : 0 ≤ ((a + b + c + d)*(2*a^4 + 3*a^3*b + 2*a^3*c + 3*a^3*d - a^2*b^2 - 3*a^2*b*c + 4*a^2*b*d - 8*a^2*c^2 - 3*a^2*c*d - a^2*d^2 + 3*a*b^3 + 4*a*b^2*c - 3*a*b^2*d - 3*a*b*c^2 - 12*a*b*c*d - 3*a*b*d^2 + 2*a*c^3 - 3*a*c^2*d + 4*a*c*d^2 + 3*a*d^3 + 2*b^4 + 3*b^3*c + 2*b^3*d - b^2*c^2 - 3*b^2*c*d - 8*b^2*d^2 + 3*b*c^3 + 4*b*c^2*d - 3*b*c*d^2 + 2*b*d^3 + 2*c^4 + 3*c^3*d - c^2*d^2 + 3*c*d^3 + 2*d^4)) := by nlinarith only [hp]
  have hd : (0 : ℝ) < ((a + 2*b + c)*(a + c + 2*d)*(2*a + b + d)*(b + 2*c + d)) := by positivity
  have heqrat : ( (a^2 - b * d)/(b + d + 2 * c) + (b^2 - c * a)/(c + a + 2 * d) + (c^2 - d * b)/(d + b + 2 * a) + (d^2 - a * c)/(a + c + 2 * b) ) - ( 0  ) = ((a + b + c + d)*(2*a^4 + 3*a^3*b + 2*a^3*c + 3*a^3*d - a^2*b^2 - 3*a^2*b*c + 4*a^2*b*d - 8*a^2*c^2 - 3*a^2*c*d - a^2*d^2 + 3*a*b^3 + 4*a*b^2*c - 3*a*b^2*d - 3*a*b*c^2 - 12*a*b*c*d - 3*a*b*d^2 + 2*a*c^3 - 3*a*c^2*d + 4*a*c*d^2 + 3*a*d^3 + 2*b^4 + 3*b^3*c + 2*b^3*d - b^2*c^2 - 3*b^2*c*d - 8*b^2*d^2 + 3*b*c^3 + 4*b*c^2*d - 3*b*c*d^2 + 2*b*d^3 + 2*c^4 + 3*c^3*d - c^2*d^2 + 3*c*d^3 + 2*d^4)) / ((a + 2*b + c)*(a + c + 2*d)*(2*a + b + d)*(b + 2*c + d)) := by
    field_simp (disch := positivity)
    <;> ring
  have hfrac := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hfrac]
example : (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d), (a^2 - b * d)/(b + d + 2 * c) + (b^2 - c * a)/(c + a + 2 * d) + (c^2 - d * b)/(d + b + 2 * a) + (d^2 - a * c)/(a + c + 2 * b) ≥ 0) := @solution
#print axioms solution
