-- Prove2me | solution 1 for WorkbookSource.base_27406
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:36:58.405755+00:00
-- url     : https://prove2.me/submissions/eff61322-2fea-4b68-af30-8068ea37f98f

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y : ℝ) (h : x + y = 2) (hx : x ≥ 0) (hy : y ≥ 0) : (x + 1) * y * (x ^ 2 + y ^ 2) ≤ 8  := by
  have helim : y = (2 - x) := by linarith only [h]
  have hsum : 0 ≤ (697/154 : ℝ) * (1) * (-160776*x^2/241859 + x)^2 + (2/83925073 : ℝ) * (1) * (x^2)^2 + (4 : ℝ) * (x) * (1 - 81*x/1232)^2 + (69/131671232 : ℝ) * (x) * (x)^2 := by positivity
  have hid : ( 8  ) - ( (x + 1) * y * (x ^ 2 + y ^ 2) ) = (697/154 : ℝ) * (1) * (-160776*x^2/241859 + x)^2 + (2/83925073 : ℝ) * (1) * (x^2)^2 + (4 : ℝ) * (x) * (1 - 81*x/1232)^2 + (69/131671232 : ℝ) * (x) * (x)^2 := by
    try simp only [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (x y : ℝ) (h : x + y = 2) (hx : x ≥ 0) (hy : y ≥ 0), (x + 1) * y * (x ^ 2 + y ^ 2) ≤ 8) := @solution
#print axioms solution
