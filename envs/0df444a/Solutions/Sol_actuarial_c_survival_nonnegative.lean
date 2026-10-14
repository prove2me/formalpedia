-- Prove2me | solution 1 for actuarial_c_survival_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T13:09:09.11993+00:00
-- url     : https://prove2.me/submissions/5fcc95f5-fc6a-4306-b7a2-813b7114c860

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_surv

open ActuarialAssurances

theorem solution (h j : ℕ) (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) : 0 ≤ surv h p j := by
  simp only [surv, alive]
  apply Finset.sum_nonneg
  intro k _
  split_ifs
  · exact mul_nonneg (hp k) (by norm_num : (0 : ℝ) ≤ 1)
  · simp

