-- Prove2me | solution 1 for actuarial_c_epv_scale
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T13:04:55.775067+00:00
-- url     : https://prove2.me/submissions/c9b16cd7-6148-4fb9-8232-82be40a89094

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_path
import Definitions.Def_actuarial_c_epv

open ActuarialAssurances

theorem solution (h : ℕ) (v c : ℝ) (b p : ℕ → ℝ) : epv h v (fun j => c*b j) p=c*epv h v b p := by
  simp only [epv]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  have hp : path h v (fun j => c * b j) k = c * path h v b k := by
    simp only [path]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    simp [mul_assoc, mul_left_comm, mul_comm]
  rw [hp]
  simp [mul_assoc, mul_left_comm, mul_comm]

