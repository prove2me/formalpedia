-- Prove2me | solution 1 for actuarial_e_realised_death_member_spouse_guarantee
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T13:08:36.507244+00:00
-- url     : https://prove2.me/submissions/8bce1370-a2f1-41e0-b869-7b212a9722f0

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_deathPV
import Definitions.Def_actuarial_e_memberPayment
import Definitions.Def_actuarial_e_guaranteePayment
import Definitions.Def_actuarial_e_spousePayment
import Definitions.Def_actuarial_e_realisedPV

open ActuarialDeathE

theorem solution (h n e r g i j : ℕ) (disc service defer retire base a b c increase : ℕ → ℝ) (replace : Bool) : realisedPV h n e r g i j disc service defer retire base a b c increase replace = deathPV h e r i disc service defer retire + ∑ t ∈ Finset.range n, disc t * (memberPayment r i t base + spousePayment h e r g i j t a b c increase replace + guaranteePayment h r g i t base) := by
  simp [ActuarialDeathE.active, ActuarialDeathE.alive, ActuarialDeathE.deathPV, ActuarialDeathE.deferred, ActuarialDeathE.guaranteePayment, ActuarialDeathE.instalment, ActuarialDeathE.memberPayment, ActuarialDeathE.realisedPV, ActuarialDeathE.regimeLump, ActuarialDeathE.retired, ActuarialDeathE.spouseDue, ActuarialDeathE.spousePayment, ActuarialJointD.alive, ActuarialJointD.dead, ActuarialJointD.expect, ActuarialJointD.mass, ActuarialJointD.onlyY, ActuarialJointD.valid]
