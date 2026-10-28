-- Prove2me | solution 1 for actuarial_f_pre88_gmp_growth_one
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:56:12.98873+00:00
-- url     : https://prove2.me/submissions/74d54d05-b7f8-4ac4-8000-03ff4cc85d4e

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_gmpPre88StatutoryGrowth

open ActuarialUnderpinsF



theorem solution
    (gpd date : ℕ) :
    gmpPre88StatutoryGrowth gpd date = 1 := by
  rfl
