-- Prove2me | solution 1 for actuarial_f_spouse_floor_monotone
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:37:40.847904+00:00
-- url     : https://prove2.me/submissions/3773becd-cfb3-464b-a031-9b499594d137

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_spouseDue
import Definitions.Def_actuarial_f_survivorFlooredInstalment

open ActuarialUnderpinsF

theorem solution (h z i j t : ℕ)
    (a b : ℕ → ℕ → ℝ) (gs : ℕ → ℕ → ℝ)
    (hg : 0 ≤ gs i t) :
    a z i * gs i t * spouseDue h i j t ≤
      survivorFlooredInstalment h z i j t a b gs := by
  have hsd : 0 ≤ spouseDue h i j t := by
    unfold spouseDue ActuarialJointD.onlyY ActuarialJointD.dead ActuarialJointD.alive
    split_ifs <;> norm_num
  unfold survivorFlooredInstalment spouseBaseAtDeath
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hg) hsd
