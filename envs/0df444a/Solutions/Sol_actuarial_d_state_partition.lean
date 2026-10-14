-- Prove2me | solution 1 for actuarial_d_state_partition
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:50:52.322841+00:00
-- url     : https://prove2.me/submissions/867da4e2-8911-4f58-8ee3-4e62de1f6aeb

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_d_dead
import Definitions.Def_actuarial_d_both
import Definitions.Def_actuarial_d_onlyX
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_neither
import Definitions.Def_actuarial_d_last

open ActuarialJointD

theorem solution (i j t : ℕ) : both i j t + onlyX i j t + onlyY i j t + neither i j t = 1 := by
  simp only [both, onlyX, onlyY, neither, dead, alive]
  by_cases hi : t ≤ i <;> by_cases hj : t ≤ j <;> simp [hi, hj]
