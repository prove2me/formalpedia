-- Prove2me | solution 1 for actuarial_c_deferred_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:54:01.774269+00:00
-- url     : https://prove2.me/submissions/177858ab-4f95-42c9-b8ba-dc5c19424a8c

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_deferred

open ActuarialAssurances

theorem solution (h a : ℕ) (v : ℝ) (b p : ℕ → ℝ) : deferred h a 0 v b p=0 := by
  simp only [deferred]
  apply Finset.sum_eq_zero
  intro j _
  simp

