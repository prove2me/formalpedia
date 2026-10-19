-- Prove2me | solution 1 for actuarial_e_disjoint_deferred_retired
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T12:20:10.111945+00:00
-- url     : https://prove2.me/submissions/868e1d0a-3085-47f3-8ba3-802ab9eb21fd

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_deferred
import Definitions.Def_actuarial_e_retired

open ActuarialDeathE

theorem solution (h e r i : ℕ) (her : e ≤ r) : deferred h e r i * retired h r i = 0 := by
  simp only [ActuarialDeathE.deferred, ActuarialDeathE.retired, ActuarialJointD.alive, ActuarialJointD.dead, ActuarialJointD.expect, ActuarialJointD.mass, ActuarialJointD.onlyY, ActuarialJointD.valid]; split_ifs <;> simp_all <;> linarith
