-- Prove2me | solution 1 for actuarial_f_member_gmp_topup_after_death
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:04:07.023747+00:00
-- url     : https://prove2.me/submissions/deb774a2-332e-4b9e-8714-974da72ed148

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_gmpMemberProtectedTopUp

open ActuarialUnderpinsF



theorem solution
    (r z i t gpd : ℕ) (dateOf : ℕ → ℕ)
    (pre88 post88 protectedExcess : ℕ → ℝ)
    (orderRate a b c ga gb gc : ℕ → ℝ)
    (h : i < t) :
    gmpMemberProtectedTopUp r z i t gpd dateOf
      pre88 post88 protectedExcess orderRate a b c ga gb gc = 0 := by
  simp [gmpMemberProtectedTopUp, memberDue, ActuarialJointD.alive, not_le.mpr h]
