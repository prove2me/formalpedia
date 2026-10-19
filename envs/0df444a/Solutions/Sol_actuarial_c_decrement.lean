-- Prove2me | solution 1 for actuarial_c_decrement
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:00:48.769285+00:00
-- url     : https://prove2.me/submissions/037224e4-6dbb-4ef1-8711-564c1a01f83c

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_surv

open ActuarialAssurances



theorem solution (h j : ℕ) (p : ℕ → ℝ) (hj : j < h) : surv h p j=p j+surv h p (j+1) := by
  unfold surv alive
  have e : ∀ k, p k * (if j ≤ k then (1:ℝ) else 0) =
      (if k = j then p k else 0) + p k * (if j+1 ≤ k then (1:ℝ) else 0) := by
    intro k; split_ifs <;> first | (exfalso; omega) | ring
  rw [Finset.sum_congr rfl (fun k _ => e k), Finset.sum_add_distrib, Finset.sum_ite_eq']
  rw [if_pos (by simp; omega)]

