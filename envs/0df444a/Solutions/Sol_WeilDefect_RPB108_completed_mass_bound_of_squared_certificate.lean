-- Prove2me | solution 1 for WeilDefect.RPB108.completed_mass_bound_of_squared_certificate
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T20:17:55.656975+00:00
-- url     : https://prove2.me/submissions/1429a344-eea5-4f42-ad77-84ef38cc0bec

import Mathlib
open scoped BigOperators
set_option autoImplicit false
theorem solution (m q k B : ℝ)
    (hk : 0 < k) (hm : m ≤ B) (hq : q ≤ (k*(B-m))^2) :
    m + Real.sqrt q/k ≤ B := by
  have hs : Real.sqrt q ≤ k*(B-m) :=
    (Real.sqrt_le_left (mul_nonneg hk.le (sub_nonneg.mpr hm))).mpr hq
  have hd : Real.sqrt q/k ≤ B-m := by
    apply (div_le_iff₀ hk).mpr
    nlinarith
  linarith
