-- Prove2me | solution 1 for actuarial_e_eligible_spouse_guarantee_overlap
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T18:45:07.54971+00:00
-- url     : https://prove2.me/submissions/eb602382-bdd8-46c4-8c16-1001a45a2a98

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

theorem solution (h r g i j t : ℕ) (c increase : ℕ → ℝ) (hr : r ≤ i) (hi : i < h) (ht : i + 1 < t) (hj : t ≤ j) (hg : t < r + g) : overlapPayment h r g i j t c increase = c (i + 1) * increase t := by
  unfold overlapPayment retired spouseDue
  have h1 : i < h ∧ r ≤ i := ⟨hi, hr⟩
  have h2 : i < j ∧ i + 1 < t ∧ t ≤ j := ⟨by omega, ht, hj⟩
  simp [h1, h2, hg]
