-- Prove2me | solution 1 for actuarial_c_premium_due_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T13:09:10.984045+00:00
-- url     : https://prove2.me/submissions/902cf27d-2d1a-4bd2-9982-1691b0624d39

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_surv
import Definitions.Def_actuarial_c_due

open ActuarialAssurances

theorem solution (h n : ℕ) (v : ℝ) (p : ℕ → ℝ) (hv : 0 ≤ v) (hp : ∀ j, 0 ≤ p j) : 0 ≤ due h n v p := by
  simp only [due]
  apply Finset.sum_nonneg
  intro j _
  apply mul_nonneg (pow_nonneg hv _)
  simp only [surv, alive]
  apply Finset.sum_nonneg
  intro k _
  split_ifs
  · exact mul_nonneg (hp k) (by norm_num : (0 : ℝ) ≤ 1)
  · simp

