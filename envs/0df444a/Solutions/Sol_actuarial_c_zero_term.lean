-- Prove2me | solution 1 for actuarial_c_zero_term
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:36.762988+00:00
-- url     : https://prove2.me/submissions/ea215862-c3a5-4c2d-8a58-69f2a69efabb

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_termPath
import Definitions.Def_actuarial_c_term

open ActuarialAssurances

theorem solution (h : ℕ) (v : ℝ) (b p : ℕ → ℝ) : term h 0 v b p=0 := by
  simp [term, termPath, death]
