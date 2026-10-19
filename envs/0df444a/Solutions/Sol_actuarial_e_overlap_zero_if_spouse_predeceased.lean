-- Prove2me | solution 1 for actuarial_e_overlap_zero_if_spouse_predeceased
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T18:45:31.395538+00:00
-- url     : https://prove2.me/submissions/1fe49177-263a-4c62-b460-7e249b817471

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

theorem solution (h r g i j t : ℕ) (c increase : ℕ → ℝ) (hj : j ≤ i) : overlapPayment h r g i j t c increase = 0 := by
  unfold overlapPayment retired spouseDue
  have : ¬ (i < j ∧ i + 1 < t ∧ t ≤ j) := by omega
  simp [this]
