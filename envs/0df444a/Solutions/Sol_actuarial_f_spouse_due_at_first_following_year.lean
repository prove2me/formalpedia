-- Prove2me | solution 1 for actuarial_f_spouse_due_at_first_following_year
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:37:25.23737+00:00
-- url     : https://prove2.me/submissions/f062b7f4-5a87-4a78-a9db-07d0f337724f

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_spouseDue

open ActuarialUnderpinsF

theorem solution (h i j : ℕ)
    (hi : i < h) (hj : i + 1 ≤ j) :
    spouseDue h i j (i + 1) = 1 := by
  unfold spouseDue ActuarialJointD.onlyY ActuarialJointD.dead ActuarialJointD.alive
  rw [if_pos hi, if_neg (by omega), if_pos hj]
  norm_num
