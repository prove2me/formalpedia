-- Prove2me | solution 1 for actuarial_f_spouse_not_after_survivor
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:32:59.395822+00:00
-- url     : https://prove2.me/submissions/9ee8a6d7-3883-41da-9dee-8841f80007ba

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_spouseDue

open ActuarialUnderpinsF

theorem solution (h i j t : ℕ)
    (hj : j < t) : spouseDue h i j t = 0 := by
  unfold spouseDue ActuarialJointD.onlyY ActuarialJointD.dead ActuarialJointD.alive
  split_ifs <;> (try norm_num) <;> omega
