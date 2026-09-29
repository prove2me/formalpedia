-- Prove2me | solution 1 for WorkbookSource.base_56570
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:48:05.771096+00:00
-- url     : https://prove2.me/submissions/133b4fe2-7b4e-45ea-8ec4-a066ef58ab21

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hab : a + b + c + d = 2) : a^4 + b^4 + c^4 + d^4 - 4 * a * b * c * d ≥ 2 * (a - b) * (c - d)  := by
  have helim : d = (-a - b - c + 2) := by linarith only [hab]
  have hsum : 0 ≤ (22 : ℝ) * (-23*a^2/154 - 5*a*b/11 - 5*a*c/11 + 8*a/11 - 2*b^2/11 - 5*b*c/11 + b - 19*c^2/154 + 9*c/11 - 9/11)^2 + (296/77 : ℝ) * (-23*a^2/148 - 85*a*b/296 - 85*a*c/296 + 35*a/148 + 49*b^2/148 - 85*b*c/296 - 137*c^2/296 + c - 49/148)^2 + (1853/518 : ℝ) * (-761*a^2/1853 - 1223*a*b/3706 - 1223*a*c/3706 + a + 315*b^2/1853 - 1223*b*c/3706 - 331*c^2/3706 - 315/1853)^2 + (147653/181594 : ℝ) * (-a^2 + 27216*a*b/147653 + 27216*a*c/147653 + 27216*b^2/147653 + 27216*b*c/147653 + c^2 - 27216/147653)^2 + (106362/147653 : ℝ) * (-a*b - a*c - b^2 - b*c + 1)^2 := by positivity
  have hid : ( a^4 + b^4 + c^4 + d^4 - 4 * a * b * c * d ) - ( 2 * (a - b) * (c - d)  ) = (22 : ℝ) * (-23*a^2/154 - 5*a*b/11 - 5*a*c/11 + 8*a/11 - 2*b^2/11 - 5*b*c/11 + b - 19*c^2/154 + 9*c/11 - 9/11)^2 + (296/77 : ℝ) * (-23*a^2/148 - 85*a*b/296 - 85*a*c/296 + 35*a/148 + 49*b^2/148 - 85*b*c/296 - 137*c^2/296 + c - 49/148)^2 + (1853/518 : ℝ) * (-761*a^2/1853 - 1223*a*b/3706 - 1223*a*c/3706 + a + 315*b^2/1853 - 1223*b*c/3706 - 331*c^2/3706 - 315/1853)^2 + (147653/181594 : ℝ) * (-a^2 + 27216*a*b/147653 + 27216*a*c/147653 + 27216*b^2/147653 + 27216*b*c/147653 + c^2 - 27216/147653)^2 + (106362/147653 : ℝ) * (-a*b - a*c - b^2 - b*c + 1)^2 := by
    try simp only [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hab : a + b + c + d = 2), a^4 + b^4 + c^4 + d^4 - 4 * a * b * c * d ≥ 2 * (a - b) * (c - d)) := @solution
#print axioms solution
