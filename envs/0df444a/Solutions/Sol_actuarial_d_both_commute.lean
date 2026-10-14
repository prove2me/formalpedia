-- Prove2me | solution 1 for actuarial_d_both_commute
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:50:52.999206+00:00
-- url     : https://prove2.me/submissions/ec365ea6-4cac-4949-a75c-d924ea088ee8

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

theorem solution (i j t : ℕ) : both i j t = both j i t := by
  simp only [last, onlyY, dead, alive, onlyX, both, neither]
  grind
