-- Prove2me | solution 1 for burau_cf_std_neg_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-09-30T22:21:08.563889+00:00
-- url     : https://prove2.me/submissions/8a763e98-4276-493a-a9b6-eec0feed50d2

import Definitions.Def_burau_std_cf

set_option autoImplicit false

/-- Negation rule, exact-division case: if `b ∣ a` then `cfStd b (-a) = [-(a/b)]`. -/
theorem solution (a b : ℤ) (ha : 0 < a) (hb : 0 < b) (hdvd : b ∣ a) :
    cfStd b (-a) = [-(a / b)] := by
  have hbne : b ≠ 0 := ne_of_gt hb
  have hdiv : a / b * b = a := Int.ediv_mul_cancel hdvd
  have hkey : -a = -(a / b) * b := by
    rw [mul_comm (-(a / b)) b, mul_neg, mul_comm b (a / b), hdiv]
  have hneg : (-a) / b = -(a / b) := by
    rw [hkey, mul_comm (-(a / b)) b, Int.mul_ediv_cancel_left _ hbne]
  have hnegmod : (-a) % b = 0 := by
    rw [hkey, mul_comm (-(a / b)) b, Int.mul_emod_right]
  rw [cfStd_cons b (-a) hbne, hneg, hnegmod, cfStd_zero]
