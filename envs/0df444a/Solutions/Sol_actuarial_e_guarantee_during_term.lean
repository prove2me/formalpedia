-- Prove2me | solution 1 for actuarial_e_guarantee_during_term
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T13:07:17.741593+00:00
-- url     : https://prove2.me/submissions/8c0a2df6-528e-4e3b-8b09-f194e00704b1

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_guaranteePayment

open ActuarialDeathE

theorem solution (h r g i t : ℕ) (base : ℕ → ℝ) (hi : r ≤ i) (hc : i < h) (hd : i < t) (hr : r ≤ t) (hg : t < r + g) : guaranteePayment h r g i t base = base t := by
  unfold guaranteePayment
  rw [if_pos ⟨hi, hc, hd, hr, hg⟩]
