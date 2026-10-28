-- Prove2me | solution 1 for actuarial_f_spouse_only_after_death
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:35:55.218984+00:00
-- url     : https://prove2.me/submissions/ae33845f-eef5-4053-b74a-2ba292dc37cf

import Mathlib


import Definitions.Def_actuarial_f_spouseDue

open ActuarialUnderpinsF

theorem solution (h i j t : ℕ)
    (hs : spouseDue h i j t = 1) : i < t ∧ t ≤ j :=
  by
  unfold spouseDue ActuarialJointD.onlyY ActuarialJointD.dead ActuarialJointD.alive at hs
  split_ifs at hs with h1 h2 h3 <;> (try norm_num at hs) <;> omega
