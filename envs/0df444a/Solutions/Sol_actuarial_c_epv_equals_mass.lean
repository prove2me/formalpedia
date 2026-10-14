-- Prove2me | solution 1 for actuarial_c_epv_equals_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-14T07:08:30.764272+00:00
-- url     : https://prove2.me/submissions/c6fdad82-a402-4fe9-816b-ada88e1b6f26

import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_path
import Definitions.Def_actuarial_c_epv
import Definitions.Def_actuarial_c_massPV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialAssurances

theorem solution (h : ℕ) (v : ℝ) (b p : ℕ → ℝ) : epv h v b p=massPV h v b p := by
  unfold epv massPV path
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ∈ Finset.range (h + 1) := by
    have hjh : j < h := Finset.mem_range.mp hj
    exact Finset.mem_range.mpr (Nat.lt_succ_of_lt hjh)
  calc
    (∑ k ∈ Finset.range (h+1),
      p k * (v^(j+1) * b j * death k j)) =
      ∑ k ∈ Finset.range (h+1),
        if k = j then p k * (v^(j+1) * b j) else 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        by_cases hkj : k = j <;> simp [death, hkj]
    _ = p j * (v^(j+1) * b j) := by
      simp [hj']
    _ = v^(j+1)*b j*p j := by ring

