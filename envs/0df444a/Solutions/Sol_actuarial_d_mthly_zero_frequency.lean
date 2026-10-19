-- Prove2me | solution 1 for actuarial_d_mthly_zero_frequency
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T11:55:18.010992+00:00
-- url     : https://prove2.me/submissions/16744403-ff8c-4ff8-af02-c953510ad772

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_mthlyPath

open ActuarialJointD

theorem solution (years : ℕ) (d b s : ℕ → ℝ) : mthlyPath years 0 d b s = 0 := by
  simp [ActuarialJointD.mthlyPath]
