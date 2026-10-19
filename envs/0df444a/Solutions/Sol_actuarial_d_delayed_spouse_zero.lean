-- Prove2me | solution 1 for actuarial_d_delayed_spouse_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T11:50:36.944364+00:00
-- url     : https://prove2.me/submissions/ee376e72-d8d9-494b-a88f-9f7427a7e84c

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_delayedSpouse
import Definitions.Def_actuarial_d_onlyY

open ActuarialJointD

theorem solution (i j t : ℕ) : delayedSpouse 0 i j t = onlyY i j t := by
  simp [ActuarialJointD.alive, ActuarialJointD.dead, ActuarialJointD.delayedSpouse, ActuarialJointD.onlyY]
