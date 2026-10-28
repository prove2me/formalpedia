-- Prove2me | solution 1 for actuarial_f_member_contingent_bridge_stops_at_death
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:55:23.970897+00:00
-- url     : https://prove2.me/submissions/a7151ad6-d771-4478-a7bf-3b9479d9d832

import Mathlib
import Definitions.Def_actuarial_f_memberContingentBridge
open ActuarialUnderpinsF

theorem solution
    (r i start stop t : ℕ) (amount : ℝ) (hi : i < t) :
    memberContingentBridge r i start stop t amount = 0 := by
  have h1 : ¬ t ≤ i := by omega
  simp [memberContingentBridge, memberDue, ActuarialJointD.alive, h1]
