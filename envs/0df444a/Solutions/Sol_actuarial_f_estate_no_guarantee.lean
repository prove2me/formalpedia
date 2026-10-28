-- Prove2me | solution 1 for actuarial_f_estate_no_guarantee
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:34:06.424089+00:00
-- url     : https://prove2.me/submissions/c1209a2d-3f60-4079-a5f0-b8564bfaada6

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_estateDue

open ActuarialUnderpinsF

theorem solution (h r i t : ℕ) :
    estateDue h r 0 i t = 0 := by
  unfold estateDue
  rw [if_neg (by omega)]
