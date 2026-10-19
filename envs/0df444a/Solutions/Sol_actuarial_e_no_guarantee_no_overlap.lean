-- Prove2me | solution 1 for actuarial_e_no_guarantee_no_overlap
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T13:17:32.091224+00:00
-- url     : https://prove2.me/submissions/b646d406-9ce0-4c29-a1ac-93a7e6774c81

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_overlapEPV

open ActuarialDeathE

theorem solution (h n r : ℕ) (p : ℕ → ℕ → ℝ) (disc basis increase : ℕ → ℝ) : overlapEPV h n r 0 p disc basis increase = 0 := by
  unfold overlapEPV ActuarialDeathE.expect ActuarialJointD.expect
  refine Finset.sum_eq_zero fun t _ => ?_
  rw [mul_eq_zero]; right
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  unfold overlapPayment retired spouseDue
  by_cases h1 : i < h ∧ r ≤ i
  · by_cases h2 : i < j ∧ i + 1 < t ∧ t ≤ j
    · have : ¬ t < r + 0 := by omega
      rw [if_neg this]; ring
    · simp [h2]
  · simp [h1]
