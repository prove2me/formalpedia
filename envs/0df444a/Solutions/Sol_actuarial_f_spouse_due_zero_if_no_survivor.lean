-- Prove2me | solution 1 for actuarial_f_spouse_due_zero_if_no_survivor
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:37:28.842973+00:00
-- url     : https://prove2.me/submissions/6e4e30f1-e7c2-4a74-9e08-39fb5ae54f07

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_spouseDue

open ActuarialUnderpinsF

theorem solution (h i j t : ℕ)
    (hj : j ≤ i) : spouseDue h i j t = 0 := by
  unfold spouseDue ActuarialJointD.onlyY ActuarialJointD.dead ActuarialJointD.alive
  split_ifs <;> (try norm_num) <;> omega
