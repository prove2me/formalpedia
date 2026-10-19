-- Prove2me | solution 1 for actuarial_e_deferred_death_mass_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T18:45:00.244892+00:00
-- url     : https://prove2.me/submissions/84c06985-6bf5-4cb2-93a4-fe1402bb9fa5

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_validLaw
import Definitions.Def_actuarial_e_deferredDeathMass

open ActuarialDeathE

theorem solution (h e r : ℕ) (p : ℕ → ℕ → ℝ) (hp : validLaw h p) : 0 ≤ deferredDeathMass h e r p := by
  unfold deferredDeathMass expect ActuarialJointD.expect
  obtain ⟨hp0, _⟩ := hp
  apply Finset.sum_nonneg; intro i hi
  apply Finset.sum_nonneg; intro j hj
  apply mul_nonneg (hp0 i hi j hj)
  unfold deferred; dsimp only; split_ifs <;> norm_num
