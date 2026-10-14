-- Prove2me | solution 1 for actuarial_d_second_zero_discount
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:39.792316+00:00
-- url     : https://prove2.me/submissions/5ce8e479-2694-43e7-ab40-c6d3ec8546b4

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_assureSecond
import Definitions.Def_actuarial_d_secondPath
import Definitions.Def_actuarial_d_expect

open ActuarialJointD

theorem solution (h : ℕ) (p : ℕ → ℕ → ℝ) : assureSecond h p (fun _ => 0) = 0 := by
  simp [expect, secondPath, assureSecond]
