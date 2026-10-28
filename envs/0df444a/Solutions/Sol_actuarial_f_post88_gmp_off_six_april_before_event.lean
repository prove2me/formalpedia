-- Prove2me | solution 1 for actuarial_f_post88_gmp_off_six_april_before_event
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:58:43.567636+00:00
-- url     : https://prove2.me/submissions/639ea8a3-0f04-4b20-b9c8-cd2501cf903c

import Mathlib
import Definitions.Def_actuarial_f_gmpSixApril
import Definitions.Def_actuarial_f_gmpPost88AprilIncrease
open ActuarialUnderpinsF

theorem solution
    (year : ℕ) (gpd date : ℕ) (orderRate : ℕ → ℝ)
    (h : date < gmpSixApril year) :
    gmpPost88AprilIncrease gpd date orderRate year = 0 := by
  unfold gmpPost88AprilIncrease
  rw [if_neg]
  rintro ⟨_, h2⟩
  omega
