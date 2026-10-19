-- Prove2me | solution 1 for actuarial_e_two_tranche_additive
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T13:20:19.248709+00:00
-- url     : https://prove2.me/submissions/01f987bd-55fe-4bdb-9d25-16ba8af073e5

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_instalment
import Definitions.Def_actuarial_e_tranchePayment

open ActuarialDeathE

theorem solution (h e r g i j t : ℕ) (base1 base2 a1 a2 b1 b2 c1 c2 inc1 inc2 : ℕ → ℝ) (replace : Bool) : tranchePayment h e r g i j t base1 base2 a1 a2 b1 b2 c1 c2 inc1 inc2 replace = instalment h e r g i j t base1 a1 b1 c1 inc1 replace + instalment h e r g i j t base2 a2 b2 c2 inc2 replace := by
  simp [ActuarialDeathE.active, ActuarialDeathE.alive, ActuarialDeathE.deferred, ActuarialDeathE.guaranteePayment, ActuarialDeathE.instalment, ActuarialDeathE.memberPayment, ActuarialDeathE.retired, ActuarialDeathE.spouseDue, ActuarialDeathE.spousePayment, ActuarialDeathE.tranchePayment, ActuarialJointD.alive, ActuarialJointD.dead, ActuarialJointD.expect, ActuarialJointD.mass, ActuarialJointD.onlyY, ActuarialJointD.valid]
