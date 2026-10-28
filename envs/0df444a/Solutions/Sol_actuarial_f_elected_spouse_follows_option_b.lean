-- Prove2me | solution 1 for actuarial_f_elected_spouse_follows_option_b
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:54:27.343411+00:00
-- url     : https://prove2.me/submissions/2670ae2a-97d9-4a26-8ebc-9cc6b9d6094e

import Mathlib
import Definitions.Def_actuarial_f_linkedSpouseBasis
open ActuarialUnderpinsF

theorem solution
    (a b : ℕ → ℝ) (sa sb : ℕ → ℕ → ℝ)
    (z i : ℕ) (hab : a z ≤ b z) :
    linkedSpouseBasis a b sa sb z i = sb z i := by
  simp [linkedSpouseBasis, hab]
