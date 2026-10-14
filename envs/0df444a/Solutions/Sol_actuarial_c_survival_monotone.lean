-- Prove2me | solution 1 for actuarial_c_survival_monotone
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T13:09:14.242302+00:00
-- url     : https://prove2.me/submissions/73d9a5ca-8f42-4603-b0f0-0142fe057fb4

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_surv

open ActuarialAssurances

theorem solution (h i j : ℕ) (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hij : i ≤ j) : surv h p j ≤ surv h p i := by
  simp only [surv, alive]
  apply Finset.sum_le_sum
  intro k _
  split_ifs with hu ht ht
  · simp
  · exact absurd (le_trans hij hu) ht
  · simpa using hp k
  · simp

