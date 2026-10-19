-- Prove2me | solution 1 for actuarial_e_spouse_due_requires_eligibility
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T13:16:37.435082+00:00
-- url     : https://prove2.me/submissions/985b640f-83ad-4890-9805-614da872b8a0

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_spouseEligible
import Definitions.Def_actuarial_e_spouseDue

open ActuarialDeathE

theorem solution (i j t : ℕ) : spouseDue i j t * (1 - spouseEligible i j) = 0 := by
  simp only [ActuarialDeathE.spouseDue, ActuarialDeathE.spouseEligible, ActuarialJointD.alive, ActuarialJointD.dead, ActuarialJointD.expect, ActuarialJointD.mass, ActuarialJointD.onlyY, ActuarialJointD.valid]; split_ifs <;> simp_all <;> linarith
