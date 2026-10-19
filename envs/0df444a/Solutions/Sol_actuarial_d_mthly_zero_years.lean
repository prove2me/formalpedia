-- Prove2me | solution 1 for actuarial_d_mthly_zero_years
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T11:54:39.800269+00:00
-- url     : https://prove2.me/submissions/971a7f44-242a-48cc-b61c-cd9cbd09c55c

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_mthlyPath

open ActuarialJointD

theorem solution (m : ℕ) (d b s : ℕ → ℝ) : mthlyPath 0 m d b s = 0 := by
  simp [ActuarialJointD.mthlyPath]
