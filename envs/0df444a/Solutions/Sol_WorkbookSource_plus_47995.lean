-- Prove2me | solution 1 for WorkbookSource.plus_47995
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:24:12.840024+00:00
-- url     : https://prove2.me/submissions/19098e01-82bd-4f01-9c05-0e502a9e367c

import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option exponentiation.threshold 4096
theorem solution : ⌊π⌋ = 3   := by
  apply Int.floor_eq_iff.mpr
  constructor
  · exact le_of_lt Real.pi_gt_three
  · norm_num
    exact Real.pi_lt_four
example : (⌊π⌋ = 3) := @solution
#print axioms solution
