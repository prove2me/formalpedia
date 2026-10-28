-- Prove2me | solution 1 for actuarial_f_post88_gmp_not_on_gpd_april
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:58:16.1288+00:00
-- url     : https://prove2.me/submissions/2a7bcbbb-2ead-457d-9c3e-e3ee00c46fe4

import Mathlib
import Definitions.Def_actuarial_f_gmpSixApril
import Definitions.Def_actuarial_f_gmpPost88AprilIncrease
open ActuarialUnderpinsF

theorem solution
    (year : ℕ) (orderRate : ℕ → ℝ) :
    gmpPost88AprilIncrease (gmpSixApril year)
      (gmpSixApril year) orderRate year = 0 := by
  unfold gmpPost88AprilIncrease
  rw [if_neg]
  rintro ⟨h1, _⟩
  exact lt_irrefl _ h1
