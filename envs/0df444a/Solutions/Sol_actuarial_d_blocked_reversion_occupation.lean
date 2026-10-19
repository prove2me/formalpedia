-- Prove2me | solution 1 for actuarial_d_blocked_reversion_occupation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T11:51:51.430994+00:00
-- url     : https://prove2.me/submissions/37933875-2951-478b-997f-5fb071bcb5a4

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_delayedSpouse
import Definitions.Def_actuarial_d_onlyY

open ActuarialJointD

theorem solution (g i j t : ℕ) : delayedSpouse g i j t = onlyY i j t - (if t < g then onlyY i j t else 0) := by
  simp only [ActuarialJointD.alive, ActuarialJointD.dead, ActuarialJointD.delayedSpouse, ActuarialJointD.onlyY]; split_ifs <;> simp_all <;> linarith
