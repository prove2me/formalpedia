-- Prove2me | solution 1 for actuarial_d_neither_commute
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:50:50.223991+00:00
-- url     : https://prove2.me/submissions/b20ad39f-d06a-4361-91c3-b82c652b286f

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

theorem solution (i j t : ℕ) : neither i j t = neither j i t := by
  simp only [last, onlyY, dead, alive, onlyX, both, neither]
  grind
