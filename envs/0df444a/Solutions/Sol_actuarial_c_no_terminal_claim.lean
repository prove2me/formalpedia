-- Prove2me | solution 1 for actuarial_c_no_terminal_claim
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:58:28.342541+00:00
-- url     : https://prove2.me/submissions/ae627ce1-e91e-4c19-aca7-2ac9f43d22d1

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_path

open ActuarialAssurances

theorem solution (h : ℕ) (v : ℝ) (b : ℕ → ℝ) : path h v b h=0 := by
  simp only [path, death]
  apply Finset.sum_eq_zero
  intro j hj
  have hne : j ≠ h := ne_of_lt (Finset.mem_range.mp hj)
  simp [Ne.symm hne]

