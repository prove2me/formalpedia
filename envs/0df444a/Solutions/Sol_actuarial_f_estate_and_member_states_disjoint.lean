-- Prove2me | solution 1 for actuarial_f_estate_and_member_states_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:38:49.756599+00:00
-- url     : https://prove2.me/submissions/82941e4a-2adc-48cd-be67-4b1fcf3c8412

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_estateDue
import Definitions.Def_actuarial_f_memberDue

open ActuarialUnderpinsF

theorem solution (h r g i t : ℕ) :
    memberDue r i t * estateDue h r g i t = 0 := by
  unfold memberDue estateDue ActuarialJointD.alive
  split_ifs <;> (try norm_num) <;> omega
