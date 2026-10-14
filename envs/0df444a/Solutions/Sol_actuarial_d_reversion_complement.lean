-- Prove2me | solution 1 for actuarial_d_reversion_complement
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:50:52.376022+00:00
-- url     : https://prove2.me/submissions/a8f7512b-223f-42a2-a970-3603b2d72b8d

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

theorem solution (i j t : ℕ) : onlyY i j t = alive j t - both i j t := by
  simp only [last, onlyY, dead, alive, onlyX, both, neither]
  grind
