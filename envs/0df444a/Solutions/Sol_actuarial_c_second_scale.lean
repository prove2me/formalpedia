-- Prove2me | solution 1 for actuarial_c_second_scale
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:54:05.430439+00:00
-- url     : https://prove2.me/submissions/abe8d6e9-c3a3-48cb-95a4-b5be5937f287

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_path
import Definitions.Def_actuarial_c_second

open ActuarialAssurances

theorem solution (h : ℕ) (v c : ℝ) (b p : ℕ → ℝ) : second h v (fun j => c*b j) p=c^2*second h v b p := by
  simp only [second]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  have hp : path h v (fun j => c * b j) k = c * path h v b k := by
    simp only [path]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    simp [mul_assoc, mul_left_comm, mul_comm]
  rw [hp, mul_pow]
  simp [mul_assoc, mul_left_comm, mul_comm]

