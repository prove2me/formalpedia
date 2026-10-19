-- Prove2me | solution 1 for actuarial_e_deathEPV_disjoint_sum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T18:41:02.858564+00:00
-- url     : https://prove2.me/submissions/3a5607d9-f880-4ac3-8356-d8b0c29f4405

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_deathEPV

open ActuarialDeathE

theorem solution (h e r : ℕ) (p : ℕ → ℕ → ℝ) (disc service defer retire : ℕ → ℝ) : deathEPV h e r p disc service defer retire = deathEPV h e r p disc service (fun t => 0) (fun t => 0) + deathEPV h e r p disc (fun t => 0) defer (fun t => 0) + deathEPV h e r p disc (fun t => 0) (fun t => 0) retire := by
  unfold deathEPV expect ActuarialJointD.expect
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  unfold deathPV regimeLump
  ring
