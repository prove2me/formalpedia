-- Prove2me | solution 1 for actuarial_d_arrears_zero_term
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:37.108418+00:00
-- url     : https://prove2.me/submissions/89a9fabf-11e2-445c-95b5-6a4a62d0d051

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_arrearsLast

open ActuarialJointD

theorem solution (h n : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) : arrearsLast h 0 p d b = 0 := by
  simp [arrearsLast, arrearsValue, arrearsPath, expect, last, onlyY, dead, alive, onlyX, both]
