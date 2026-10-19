-- Prove2me | solution 1 for actuarial_e_spouse_ineligible_if_predeceased
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T13:19:20.199375+00:00
-- url     : https://prove2.me/submissions/8ef22915-e0ab-49d4-9a6e-ff10578a2529

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_spouseEligible

open ActuarialDeathE

theorem solution (i j : ℕ) (h : j ≤ i) : spouseEligible i j = 0 := by
  simp only [ActuarialDeathE.spouseEligible, ActuarialJointD.alive, ActuarialJointD.dead, ActuarialJointD.expect, ActuarialJointD.mass, ActuarialJointD.onlyY, ActuarialJointD.valid]; split_ifs <;> simp_all <;> linarith
