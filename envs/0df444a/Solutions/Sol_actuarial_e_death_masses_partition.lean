-- Prove2me | solution 1 for actuarial_e_death_masses_partition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T18:44:53.319713+00:00
-- url     : https://prove2.me/submissions/da4a903b-bb03-4354-bca0-e74bc64248a9

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_expect
import Definitions.Def_actuarial_e_activeDeathMass
import Definitions.Def_actuarial_e_deferredDeathMass
import Definitions.Def_actuarial_e_retiredDeathMass

open ActuarialDeathE

theorem solution (h e r : ℕ) (p : ℕ → ℕ → ℝ) (he : e ≤ r) : activeDeathMass h e p + deferredDeathMass h e r p + retiredDeathMass h r p = expect h p (fun i j => if i < h then (1 : ℝ) else 0) := by
  unfold activeDeathMass deferredDeathMass retiredDeathMass expect ActuarialJointD.expect
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  unfold active deferred retired
  dsimp only
  split_ifs <;> first | omega | ring
