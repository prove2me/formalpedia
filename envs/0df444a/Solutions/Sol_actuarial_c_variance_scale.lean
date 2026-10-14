-- Prove2me | solution 1 for actuarial_c_variance_scale
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T13:04:56.444328+00:00
-- url     : https://prove2.me/submissions/cab7bde9-7632-4d29-8c7f-d0bec88da6e1

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_path
import Definitions.Def_actuarial_c_epv
import Definitions.Def_actuarial_c_second
import Definitions.Def_actuarial_c_variance

open ActuarialAssurances

theorem solution (h : ℕ) (v c : ℝ) (b p : ℕ → ℝ) : variance h v (fun j => c*b j) p=c^2*variance h v b p := by
  simp only [variance]
  have hs : second h v (fun j => c * b j) p = c ^ 2 * second h v b p := by
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
  have he : epv h v (fun j => c * b j) p = c * epv h v b p := by
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
  rw [hs, he, mul_pow]
  ring

