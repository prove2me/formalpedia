-- Prove2me | solution 1 for actuarial_f_post88_gmp_no_part_year_scaling
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:05:40.865182+00:00
-- url     : https://prove2.me/submissions/17f8e182-a4d7-4ed3-ad75-36f7340c312d

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_lpiRate
import Definitions.Def_actuarial_f_gmpSixApril
import Definitions.Def_actuarial_f_gmpPost88AprilIncrease

open ActuarialUnderpinsF



theorem solution
    (gpd date year : ℕ) (orderRate : ℕ → ℝ)
    (hgpd : gpd < gmpSixApril year)
    (hevent : gmpSixApril year ≤ date) :
    gmpPost88AprilIncrease gpd date orderRate year =
      lpiRate 0 (3 / 100) (orderRate year) := by
  unfold gmpPost88AprilIncrease gmpStatutoryAprilEligible gmpStatutoryPost88OrderRate
  rw [if_pos ⟨hgpd, hevent⟩]
