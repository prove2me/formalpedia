-- Prove2me | solution 1 for actuarial_e_service_refund_only
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T13:09:36.657541+00:00
-- url     : https://prove2.me/submissions/d542d60b-883d-45e9-a29a-6bf57c995534

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_serviceBundle

open ActuarialDeathE

theorem solution (k : ℝ) (salary accrued contributions : ℕ → ℝ) (t : ℕ) : serviceBundle k salary accrued contributions false false true t = contributions t := by
  simp only [ActuarialDeathE.salaryMultiple, ActuarialDeathE.serviceBundle, ActuarialJointD.alive, ActuarialJointD.dead, ActuarialJointD.expect, ActuarialJointD.mass, ActuarialJointD.onlyY, ActuarialJointD.valid, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
