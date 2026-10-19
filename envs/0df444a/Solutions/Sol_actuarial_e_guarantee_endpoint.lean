-- Prove2me | solution 1 for actuarial_e_guarantee_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T13:07:27.827434+00:00
-- url     : https://prove2.me/submissions/f30c3065-fec6-435a-9283-c2bc2a864366

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_guaranteePayment

open ActuarialDeathE

theorem solution (h r g i : ℕ) (base : ℕ → ℝ) : guaranteePayment h r g i (r + g) base = 0 := by
  simp only [ActuarialDeathE.guaranteePayment, ActuarialJointD.alive, ActuarialJointD.dead, ActuarialJointD.expect, ActuarialJointD.mass, ActuarialJointD.onlyY, ActuarialJointD.valid, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
