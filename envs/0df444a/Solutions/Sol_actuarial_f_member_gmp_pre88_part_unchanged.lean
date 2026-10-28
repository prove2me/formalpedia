-- Prove2me | solution 1 for actuarial_f_member_gmp_pre88_part_unchanged
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:04:27.188992+00:00
-- url     : https://prove2.me/submissions/7c501e7a-ebec-4de8-827d-9b75aa22a3d7

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_gmpPost88StatutoryGrowth
import Definitions.Def_actuarial_f_gmpMemberMinimumAtPayment

open ActuarialUnderpinsF



theorem solution
    (pre88 post88 : ℝ) (gpd date : ℕ)
    (orderRate : ℕ → ℝ) :
    gmpMemberMinimumAtPayment pre88 post88 gpd date orderRate =
      pre88 + post88 * gmpPost88StatutoryGrowth gpd date orderRate := by
  rfl
