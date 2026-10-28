-- Prove2me | solution 1 for actuarial_f_post88_gmp_not_before_gpd
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:00:23.937613+00:00
-- url     : https://prove2.me/submissions/31995bd2-1fdd-4b45-92d1-17515e68636e

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_gmpPost88AprilIncrease

open ActuarialUnderpinsF



theorem solution
    (gpd date year : ℕ) (orderRate : ℕ → ℝ)
    (h : date ≤ gpd) :
    gmpPost88AprilIncrease gpd date orderRate year = 0 := by
  unfold gmpPost88AprilIncrease gmpStatutoryAprilEligible
  rw [if_neg (fun hh => absurd (lt_of_lt_of_le hh.1 hh.2) (by omega))]
