-- Prove2me | solution 1 for WorkbookSource.base_28566
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:48:03.847283+00:00
-- url     : https://prove2.me/submissions/33425c66-2874-419a-b1a4-376be6bad588

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : 7 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 + 6 * a * b * c ≥ 23 * (a ^ 2 + b ^ 2 + c ^ 2)  := by
  have helim : c = (-a - b + 3) := by linarith only [habc]
  have hsum : 0 ≤ (360 : ℝ) * (197*a^2/810 + 373*a*b/1620 - 103*a/120 + 197*b^2/810 - 103*b/120 + 1)^2 + (6359/360 : ℝ) * (-11476*a^2/19077 - 15202*a*b/19077 + 5719*a/6359 - 9556*b^2/19077 + b)^2 + (21472/6359 : ℝ) * (691*a^2/3294 - 691*a*b/1647 + a - 2603*b^2/3294)^2 + (9776/14823 : ℝ) * (-a^2/2 + a*b - b^2/2)^2 := by positivity
  have hid : ( 7 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 + 6 * a * b * c ) - ( 23 * (a ^ 2 + b ^ 2 + c ^ 2)  ) = (360 : ℝ) * (197*a^2/810 + 373*a*b/1620 - 103*a/120 + 197*b^2/810 - 103*b/120 + 1)^2 + (6359/360 : ℝ) * (-11476*a^2/19077 - 15202*a*b/19077 + 5719*a/6359 - 9556*b^2/19077 + b)^2 + (21472/6359 : ℝ) * (691*a^2/3294 - 691*a*b/1647 + a - 2603*b^2/3294)^2 + (9776/14823 : ℝ) * (-a^2/2 + a*b - b^2/2)^2 := by
    try simp only [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), 7 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 + 6 * a * b * c ≥ 23 * (a ^ 2 + b ^ 2 + c ^ 2)) := @solution
#print axioms solution
