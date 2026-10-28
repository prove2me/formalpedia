-- Prove2me | solution 1 for actuarial_f_member_tranche_two_before_award
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:39:41.822189+00:00
-- url     : https://prove2.me/submissions/a209e1d2-0a6a-4f62-8fec-24f04ed7dab9

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_memberTrancheTwo

open ActuarialUnderpinsF

theorem solution (r z i t : ℕ)
    (c g1 : ℕ → ℝ) (ht : t < r) :
    memberTrancheTwo r z i t c g1 = 0 := by
  have hm : memberDue r i t = 0 := by
    unfold memberDue
    rw [if_neg (by omega)]
  unfold memberTrancheTwo
  rw [hm, mul_zero]
