-- Prove2me | solution 1 for actuarial_d_last_partition
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:38.392869+00:00
-- url     : https://prove2.me/submissions/21b6a0a0-78c4-4ee6-bfe1-4d3368aa1db0

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

theorem solution (i j t : ℕ) : last i j t = both i j t + onlyX i j t + onlyY i j t := by
  simp [last, onlyY, dead, alive, onlyX, both, neither]
