-- Prove2me | solution 1 for actuarial_c_survival_after_horizon
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:54:03.287627+00:00
-- url     : https://prove2.me/submissions/0509bcdd-3673-4b7f-997a-f38ced609335

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_surv

open ActuarialAssurances

theorem solution (h j : ℕ) (p : ℕ → ℝ) (hj : h < j) : surv h p j=0 := by
  simp only [surv, alive]
  apply Finset.sum_eq_zero
  intro k hk
  have hk' : k ≤ h := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have : ¬ j ≤ k := not_le_of_gt (lt_of_le_of_lt hk' hj)
  simp [this]

