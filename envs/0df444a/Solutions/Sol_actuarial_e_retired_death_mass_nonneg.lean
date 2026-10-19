-- Prove2me | solution 1 for actuarial_e_retired_death_mass_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:31:12.051601+00:00
-- url     : https://prove2.me/submissions/cef6a8bf-e1b6-4335-81f0-360a2274cca2

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_validLaw
import Definitions.Def_actuarial_e_retiredDeathMass

open ActuarialDeathE



theorem solution (h r : ℕ) (p : ℕ → ℕ → ℝ) (hp : validLaw h p) : 0 ≤ retiredDeathMass h r p := by
  unfold retiredDeathMass expect ActuarialJointD.expect
  obtain ⟨hp0, _⟩ := hp
  apply Finset.sum_nonneg; intro i hi
  apply Finset.sum_nonneg; intro j hj
  apply mul_nonneg (hp0 i hi j hj)
  unfold retired; dsimp only; split_ifs <;> norm_num

