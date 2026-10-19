-- Prove2me | solution 1 for actuarial_e_overlap_zero_death_before_retirement
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T18:45:21.81141+00:00
-- url     : https://prove2.me/submissions/1bfe5b29-00dc-4eeb-b967-f182b856f808

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

theorem solution (h r g i j t : ℕ) (c increase : ℕ → ℝ) (hi : i < r) : overlapPayment h r g i j t c increase = 0 := by
  unfold overlapPayment retired spouseDue
  have : ¬ (i < h ∧ r ≤ i) := by omega
  simp [this]
