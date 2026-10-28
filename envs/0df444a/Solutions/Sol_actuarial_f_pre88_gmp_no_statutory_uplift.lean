-- Prove2me | solution 1 for actuarial_f_pre88_gmp_no_statutory_uplift
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:57:16.345351+00:00
-- url     : https://prove2.me/submissions/2adc5e95-3da4-403d-961a-5212ee09f2dd

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_gmpPre88StatutoryIncrease

open ActuarialUnderpinsF



theorem solution
    (gpd date year : ℕ) :
    gmpPre88StatutoryIncrease gpd date year = 0 := by
  rfl
