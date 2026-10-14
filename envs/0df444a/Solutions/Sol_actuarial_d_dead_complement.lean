-- Prove2me | solution 1 for actuarial_d_dead_complement
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:37.342082+00:00
-- url     : https://prove2.me/submissions/89d58e68-466a-429e-8b3d-8b44cee6ce4b

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

theorem solution (i j t : ℕ) : dead i t + alive i t = 1 := by
  simp [last, onlyY, dead, alive, onlyX, both, neither]
