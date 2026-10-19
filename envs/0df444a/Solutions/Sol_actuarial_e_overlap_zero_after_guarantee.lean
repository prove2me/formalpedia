-- Prove2me | solution 1 for actuarial_e_overlap_zero_after_guarantee
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T18:45:14.592932+00:00
-- url     : https://prove2.me/submissions/20736d94-fd4b-43cf-9320-e5e54548f3a8

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_overlapPayment

open ActuarialDeathE

theorem solution (h r g i j t : ℕ) (c increase : ℕ → ℝ) (ht : r + g ≤ t) : overlapPayment h r g i j t c increase = 0 := by
  unfold overlapPayment retired spouseDue
  have : ¬ t < r + g := by omega
  simp [this]
