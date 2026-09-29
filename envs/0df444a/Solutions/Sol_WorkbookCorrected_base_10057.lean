-- Prove2me | solution 1 for WorkbookCorrected.base_10057
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T11:14:11.039961+00:00
-- url     : https://prove2.me/submissions/ec6074c3-d4ec-472e-afe0-463fa2de2f46

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
private lemma p2mUpperBound (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 9) : x * y + y * z + z * x ≤ 27  := by
  have helim0 : z = (-x - y + 9) := by
    have hh := h
    linarith only [hh]
  have hsum : 0 ≤ (27 : ℝ) * (1) * (-x/6 - y/6 + 1)^2 + (1/4 : ℝ) * (1) * (-x + y)^2 := by positivity
  have hid : ( 27  ) - ( x * y + y * z + z * x ) = (27 : ℝ) * (1) * (-x/6 - y/6 + 1)^2 + (1/4 : ℝ) * (1) * (-x + y)^2 := by
    try simp only [helim0]
    ring
  linarith only [hsum, hid]
theorem solution : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 9), x * y + y * z + z * x ≤ 27) ∧ (∃ x y z : ℝ, (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x + y + z = 9) ∧ ( x * y + y * z + z * x  =  27  )) := by
  constructor
  · exact p2mUpperBound
  · refine ⟨3, 3, 3, ?_⟩ <;> norm_num
example : ((∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 9), x * y + y * z + z * x ≤ 27) ∧ (∃ x y z : ℝ, (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x + y + z = 9) ∧ ( x * y + y * z + z * x  =  27  ))) := @solution
#print axioms solution
