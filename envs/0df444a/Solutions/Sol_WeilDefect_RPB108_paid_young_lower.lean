-- Prove2me | solution 1 for WeilDefect.RPB108.paid_young_lower
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T20:18:30.688978+00:00
-- url     : https://prove2.me/submissions/00129608-4a4b-4d57-bf54-ccbb04eedd9d

import Theorems.Thm_WeilDefect_RPB108_paid_young_completed_square
import Mathlib
open scoped BigOperators
set_option autoImplicit false
open WeilDefect.RPB108
theorem solution (A M theta x y : ℝ) (ht : theta < 1) :
    (A-M^2/(1-theta))*x^2+theta*y^2 ≤ A*x^2-2*M*|x*y|+y^2 := by
  have hid := paid_young_completed_square A M theta |x| |y| ht
  have hp : 0 ≤ (M*|x|-(1-theta)*|y|)^2/(1-theta) :=
    div_nonneg (sq_nonneg _) (sub_pos.mpr ht).le
  simp only [sq_abs] at hid
  rw [abs_mul]
  nlinarith only [hid, hp]
