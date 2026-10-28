-- Prove2me | solution 1 for actuarial_f_spouse_not_after_member_censor
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:33:07.098234+00:00
-- url     : https://prove2.me/submissions/af577fc8-a037-4910-9d2f-d23e82073400

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_spouseDue

open ActuarialUnderpinsF

theorem solution (h j t : ℕ) :
    spouseDue h h j t = 0 := by
  unfold spouseDue
  rw [if_neg (lt_irrefl h)]
