-- Prove2me | solution 1 for actuarial_f_member_gmp_topup_before_gpd
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:59:39.979007+00:00
-- url     : https://prove2.me/submissions/3ac99bba-2ff1-43c1-874d-13877b2cffa6

import Mathlib
import Definitions.Def_actuarial_f_gmpMemberProtectedTopUp
open ActuarialUnderpinsF

theorem solution
    (r z i t gpd : ℕ) (dateOf : ℕ → ℕ)
    (pre88 post88 protectedExcess : ℕ → ℝ)
    (orderRate a b c ga gb gc : ℕ → ℝ)
    (h : dateOf t < gpd) :
    gmpMemberProtectedTopUp r z i t gpd dateOf
      pre88 post88 protectedExcess orderRate a b c ga gb gc = 0 := by
  unfold gmpMemberProtectedTopUp
  rw [if_neg (by omega)]
