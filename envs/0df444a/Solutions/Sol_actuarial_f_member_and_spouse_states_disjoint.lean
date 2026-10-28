-- Prove2me | solution 1 for actuarial_f_member_and_spouse_states_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:38:43.369384+00:00
-- url     : https://prove2.me/submissions/bd9575f0-1d62-4010-b064-d2314b036ef1

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_memberDue
import Definitions.Def_actuarial_f_spouseDue

open ActuarialUnderpinsF

theorem solution (h r i j t : ℕ) :
    memberDue r i t * spouseDue h i j t = 0 := by
  unfold memberDue spouseDue ActuarialJointD.onlyY ActuarialJointD.dead ActuarialJointD.alive
  split_ifs <;> (try norm_num) <;> omega
