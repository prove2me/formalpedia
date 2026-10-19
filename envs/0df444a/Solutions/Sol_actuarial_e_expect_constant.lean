-- Prove2me | solution 1 for actuarial_e_expect_constant
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T13:06:36.480722+00:00
-- url     : https://prove2.me/submissions/f47b219d-d257-41e5-886d-c303a456310f

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_validLaw
import Definitions.Def_actuarial_e_expect

open ActuarialDeathE

theorem solution (h : ℕ) (p : ℕ → ℕ → ℝ) (k : ℝ) (hp : validLaw h p) : expect h p (fun i j => k) = k := by
  obtain ⟨-, hm⟩ := hp
  unfold ActuarialJointD.mass at hm
  unfold ActuarialDeathE.expect ActuarialJointD.expect
  simp_rw [← Finset.sum_mul]
  rw [hm, one_mul]
