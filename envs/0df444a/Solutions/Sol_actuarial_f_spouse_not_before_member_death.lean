-- Prove2me | solution 1 for actuarial_f_spouse_not_before_member_death
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:32:52.648186+00:00
-- url     : https://prove2.me/submissions/f7a9b094-1a29-4c55-b813-1ca8854bc1ee

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_spouseDue

open ActuarialUnderpinsF

theorem solution (h i j t : ℕ)
    (ht : t ≤ i) : spouseDue h i j t = 0 := by
  unfold spouseDue ActuarialJointD.onlyY ActuarialJointD.dead ActuarialJointD.alive
  split_ifs <;> (try norm_num) <;> omega
