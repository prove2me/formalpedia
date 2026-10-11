-- Prove2me | solution 1 for WeilDefect.RPB108.paid_young_completed_square
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T20:18:21.823397+00:00
-- url     : https://prove2.me/submissions/3b9dc49d-21e6-4737-b917-9cda232a54dd

import Mathlib
open scoped BigOperators
set_option autoImplicit false
theorem solution (A M theta x y : ℝ) (ht : theta < 1) :
    A*x^2-2*M*x*y+y^2-((A-M^2/(1-theta))*x^2+theta*y^2) =
      (M*x-(1-theta)*y)^2/(1-theta) := by
  have hn : 1-theta ≠ 0 := ne_of_gt (sub_pos.mpr ht)
  field_simp
  ring
