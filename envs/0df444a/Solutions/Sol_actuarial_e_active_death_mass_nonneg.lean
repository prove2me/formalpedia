-- Prove2me | solution 1 for actuarial_e_active_death_mass_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T18:44:45.177352+00:00
-- url     : https://prove2.me/submissions/6ddbbffb-016d-4229-80f9-01f123185f8c

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_validLaw
import Definitions.Def_actuarial_e_activeDeathMass

open ActuarialDeathE

theorem solution (h e : ℕ) (p : ℕ → ℕ → ℝ) (hp : validLaw h p) : 0 ≤ activeDeathMass h e p := by
  unfold activeDeathMass expect ActuarialJointD.expect
  obtain ⟨hp0, _⟩ := hp
  apply Finset.sum_nonneg; intro i hi
  apply Finset.sum_nonneg; intro j hj
  apply mul_nonneg (hp0 i hi j hj)
  unfold active; dsimp only; split_ifs <;> norm_num
