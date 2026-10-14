-- Prove2me | solution 1 for actuarial_c_path_scale
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:50:51.699742+00:00
-- url     : https://prove2.me/submissions/ef3b86c4-2a01-4cbf-9608-1f31f7e5513c

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_path

open ActuarialAssurances

theorem solution (h k : ℕ) (v c : ℝ) (b : ℕ → ℝ) : path h v (fun j => c*b j) k=c*path h v b k := by
  simp only [path]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  simp [mul_assoc, mul_left_comm, mul_comm]

