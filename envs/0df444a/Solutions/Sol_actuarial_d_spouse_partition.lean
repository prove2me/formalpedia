-- Prove2me | solution 1 for actuarial_d_spouse_partition
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:50:53.766068+00:00
-- url     : https://prove2.me/submissions/1138e873-7bdc-41d1-b914-86d8987eb133

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

theorem solution (i j t : ℕ) : alive j t = both i j t + onlyY i j t := by
  simp only [both, onlyY, dead, alive]
  by_cases hi : t ≤ i <;> by_cases hj : t ≤ j <;> simp [hi, hj]

