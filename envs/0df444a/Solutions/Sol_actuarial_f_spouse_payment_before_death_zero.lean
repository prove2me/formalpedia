-- Prove2me | solution 1 for actuarial_f_spouse_payment_before_death_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:37:47.621601+00:00
-- url     : https://prove2.me/submissions/93d12511-6749-4967-9165-24928bddd212

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_spouseInstalment

open ActuarialUnderpinsF

theorem solution (h z i j t : ℕ)
    (s : ℕ → ℕ → ℝ) (gs : ℕ → ℕ → ℝ)
    (ht : t ≤ i) : spouseInstalment h z i j t s gs = 0 := by
  have hsd : spouseDue h i j t = 0 := by
    unfold spouseDue ActuarialJointD.onlyY ActuarialJointD.dead ActuarialJointD.alive
    split_ifs <;> (try norm_num) <;> omega
  unfold spouseInstalment
  rw [hsd, mul_zero]
