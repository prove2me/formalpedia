-- Prove2me | solution 1 for actuarial_c_path_value_by_year
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:04:15.773993+00:00
-- url     : https://prove2.me/submissions/3ada3f6c-3348-4009-879b-7cb7edc89022

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_path
import Definitions.Def_actuarial_c_death

open ActuarialAssurances



theorem solution (h k : ℕ) (v : ℝ) (b : ℕ → ℝ) :
    path h v b k = if k < h then v^(k+1)*b k else 0 := by
  unfold path death; simp only [mul_ite, mul_one, mul_zero]; rw [Finset.sum_ite_eq]; simp [Finset.mem_range]

