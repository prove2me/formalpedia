-- Prove2me | solution 1 for WorkbookSource.base_14166
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T07:46:30.807713+00:00
-- url     : https://prove2.me/submissions/d51b90a4-5cf3-4821-a116-c13dd60e0682

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hd : d ≥ 0) (hab : a + b + c + d = 1) : 5 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) + 2 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 2 ≥ 1 + 6 * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3)  := by
  have helim : d = (-a - b - c + 1) := by linarith only [hab]
  have hsum : 0 ≤ (26 : ℝ) * (a^2/13 + 7*a*b/13 + 7*a*c/13 - a/13 + 4*b^2/13 + b*c - 4*b/13 + 4*c^2/13 - 4*c/13)^2 + (240/13 : ℝ) * (3*a^2/8 + 7*a*b/20 + a*c - 3*a/8 - b^2/8 + b/8 + c^2/5 - c/5)^2 + (81/5 : ℝ) * (5*a^2/18 + a*b - 5*a/18 + 5*b^2/18 - 5*b/18 - 2*c^2/9 + 2*c/9)^2 + (4 : ℝ) * (a^2/2 - a/2 + b^2/2 - b/2 - c^2 + c)^2 + (3 : ℝ) * (a^2 - a - b^2 + b)^2 := by positivity
  have hid : ( 5 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) + 2 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 2 ) - ( 1 + 6 * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3)  ) = (26 : ℝ) * (a^2/13 + 7*a*b/13 + 7*a*c/13 - a/13 + 4*b^2/13 + b*c - 4*b/13 + 4*c^2/13 - 4*c/13)^2 + (240/13 : ℝ) * (3*a^2/8 + 7*a*b/20 + a*c - 3*a/8 - b^2/8 + b/8 + c^2/5 - c/5)^2 + (81/5 : ℝ) * (5*a^2/18 + a*b - 5*a/18 + 5*b^2/18 - 5*b/18 - 2*c^2/9 + 2*c/9)^2 + (4 : ℝ) * (a^2/2 - a/2 + b^2/2 - b/2 - c^2 + c)^2 + (3 : ℝ) * (a^2 - a - b^2 + b)^2 := by
    rw [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c d : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hd : d ≥ 0) (hab : a + b + c + d = 1), 5 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) + 2 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 2 ≥ 1 + 6 * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3)) := @solution
#print axioms solution
