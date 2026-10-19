-- Prove2me | solution 1 for actuarial_e_expect_add
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T13:06:24.681697+00:00
-- url     : https://prove2.me/submissions/ebf2774b-3d38-465c-bbbb-98f6bb653ea8

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_expect

open ActuarialDeathE

theorem solution (h : ℕ) (p f g : ℕ → ℕ → ℝ) : expect h p (fun i j => f i j + g i j) = expect h p f + expect h p g := by
  simp only [ActuarialDeathE.expect, ActuarialJointD.alive, ActuarialJointD.dead, ActuarialJointD.expect, ActuarialJointD.mass, ActuarialJointD.onlyY, ActuarialJointD.valid]
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  repeat refine Finset.sum_congr rfl fun _ _ => ?_
  beta_reduce
  ring
