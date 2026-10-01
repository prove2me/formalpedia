-- Prove2me | solution 1 for burau_cf_std_add_divisor
-- status  : ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-09-30T22:06:48.011969+00:00
-- url     : https://prove2.me/submissions/2102d43d-4a0a-4edb-b28d-df3c7d4520da

import Definitions.Def_burau_std_cf

set_option autoImplicit false

/-- **Shift lemma**: adding `r` to the dividend increases the first quotient by one and leaves the
remainder unchanged. This is the step that makes the two Euclidean descent chains merge. -/
theorem solution (r a : ℤ) (hr : r ≠ 0) :
    cfStd r (r + a) = (a / r + 1) :: cfStd (a % r) r := by
  rw [cfStd_cons r (r + a) hr]
  have hdiv : (r + a) / r = a / r + 1 := by
    rw [show r + a = a + r * 1 by ring, Int.add_mul_ediv_left a 1 hr]
  have hmod : (r + a) % r = a % r := by
    rw [show r + a = a + r * 1 by ring, Int.add_mul_emod_self_left]
  rw [hdiv, hmod]
