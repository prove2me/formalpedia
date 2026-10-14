-- Prove2me | solution 1 for actuarial_d_only_swap
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:38.793001+00:00
-- url     : https://prove2.me/submissions/ddb58f4c-ec80-4b72-97da-e76aa08de47a

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

theorem solution (i j t : ℕ) : onlyY i j t = onlyX j i t := by
  simp [last, onlyY, dead, alive, onlyX, both, neither]
