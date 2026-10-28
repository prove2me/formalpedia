-- Prove2me | solution 1 for actuarial_f_post88_gmp_full_rate_at_april
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:01:18.479764+00:00
-- url     : https://prove2.me/submissions/d7f019b4-f21e-4665-9b63-9d43e66998bc

import Mathlib
import Definitions.Def_actuarial_f_gmpSixApril
import Definitions.Def_actuarial_f_gmpStatutoryPost88OrderRate
import Definitions.Def_actuarial_f_gmpPost88AprilIncrease
open ActuarialUnderpinsF

theorem solution
    (gpd year : ℕ) (orderRate : ℕ → ℝ)
    (h : gpd < gmpSixApril year) :
    gmpPost88AprilIncrease gpd (gmpSixApril year) orderRate year =
      gmpStatutoryPost88OrderRate orderRate year := by
  unfold gmpPost88AprilIncrease
  rw [if_pos ⟨h, le_refl _⟩]
