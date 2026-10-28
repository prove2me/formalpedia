-- Prove2me | solution 1 for actuarial_f_bounded_growth_april_example
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:52:35.578986+00:00
-- url     : https://prove2.me/submissions/18cc0528-8986-45f4-8e2d-926a38717e2a

import Mathlib
import Definitions.Def_actuarial_f_gmpBoundedPost88Growth
open ActuarialUnderpinsF

theorem solution :
    gmpBoundedPost88Growth 20261001 20270406
      (fun _ => (7/100 : ℝ)) = (103/100 : ℝ) := by
  norm_num [gmpBoundedPost88Growth, gmpDateYear, Finset.prod_range_succ, gmpPost88AprilIncrease,
    gmpStatutoryAprilEligible, gmpSixApril, gmpStatutoryPost88OrderRate, lpiRate]
