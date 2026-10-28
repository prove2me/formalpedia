-- Prove2me | solution 1 for actuarial_f_bridge_pays_zero_after_cessation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:39:30.603923+00:00
-- url     : https://prove2.me/submissions/8b8b8658-cd23-4468-9b61-7227809715d7

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_bridgeInstalment

open ActuarialUnderpinsF

theorem solution (start stop t : ℕ)
    (amount : ℝ) (ht : stop ≤ t) :
    bridgeInstalment start stop t amount = 0 := by
  unfold bridgeInstalment bridgeDue
  rw [if_neg (by omega), mul_zero]
