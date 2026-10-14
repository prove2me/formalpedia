-- Prove2me | solution 1 for actuarial_d_member_partition
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:50:53.233537+00:00
-- url     : https://prove2.me/submissions/c2b72511-dcf3-46b5-89e3-5292e06ffa20

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

theorem solution (i j t : ℕ) : alive i t = both i j t + onlyX i j t := by
  simp only [both, onlyX, dead, alive]
  by_cases hj : t ≤ j <;> by_cases hi : t ≤ i <;> simp [hi, hj]

