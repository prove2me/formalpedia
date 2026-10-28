-- Prove2me | solution 1 for actuarial_f_spouse_start_after_death
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:33:15.481021+00:00
-- url     : https://prove2.me/submissions/9ddb983c-cee2-413d-ac40-37861643e22b

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_spouseDue

open ActuarialUnderpinsF

theorem solution (h i j : ℕ) :
    spouseDue h i j i = 0 := by
  unfold spouseDue ActuarialJointD.onlyY ActuarialJointD.dead ActuarialJointD.alive
  split_ifs <;> (try norm_num) <;> omega
