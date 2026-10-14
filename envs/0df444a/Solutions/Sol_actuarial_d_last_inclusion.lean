-- Prove2me | solution 1 for actuarial_d_last_inclusion
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:50:53.53005+00:00
-- url     : https://prove2.me/submissions/d2450af7-454c-47bd-90a1-f18fe4477cba

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

theorem solution (i j t : ℕ) : last i j t = alive i t + alive j t - both i j t := by
  simp only [last, onlyY, dead, alive, onlyX, both, neither]
  grind
