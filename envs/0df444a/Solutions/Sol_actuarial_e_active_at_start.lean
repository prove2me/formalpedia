-- Prove2me | solution 1 for actuarial_e_active_at_start
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T12:11:18.916065+00:00
-- url     : https://prove2.me/submissions/16ade0cc-f334-442e-ad64-a00acaf25d11

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_active

open ActuarialDeathE

theorem solution (h e : ℕ) (he : 0 < h) (he2 : 0 < e) : active h e 0 = 1 := by
  simp only [ActuarialDeathE.active, ActuarialJointD.alive, ActuarialJointD.dead, ActuarialJointD.expect, ActuarialJointD.mass, ActuarialJointD.onlyY, ActuarialJointD.valid]; split_ifs <;> simp_all <;> linarith
