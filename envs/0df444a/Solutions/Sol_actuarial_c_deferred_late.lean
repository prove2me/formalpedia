-- Prove2me | solution 1 for actuarial_c_deferred_late
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:54:02.659563+00:00
-- url     : https://prove2.me/submissions/5d042bab-c4f9-4223-a23d-64b37420a98d

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_deferred

open ActuarialAssurances

theorem solution (h a n : ℕ) (v : ℝ) (b p : ℕ → ℝ) (ha : h ≤ a) : deferred h a n v b p=0 := by
  simp only [deferred]
  apply Finset.sum_eq_zero
  intro j hj
  have hlt : j < a := lt_of_lt_of_le (Finset.mem_range.mp hj) ha
  simp [not_le_of_gt hlt]

