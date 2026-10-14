-- Prove2me | solution 1 for actuarial_d_member_only_complement
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:50:54.204965+00:00
-- url     : https://prove2.me/submissions/47c4e2f2-38df-4395-9404-db88ed2ec779

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

theorem solution (i j t : ℕ) : onlyX i j t = alive i t - both i j t := by
  simp only [last, onlyY, dead, alive, onlyX, both, neither]
  grind
