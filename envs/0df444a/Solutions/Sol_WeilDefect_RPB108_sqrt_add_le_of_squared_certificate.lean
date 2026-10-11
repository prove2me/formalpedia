-- Prove2me | solution 1 for WeilDefect.RPB108.sqrt_add_le_of_squared_certificate
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T20:17:46.463919+00:00
-- url     : https://prove2.me/submissions/beeedd51-4761-4587-954c-690ac47fa38c

import Mathlib
open scoped BigOperators
set_option autoImplicit false
theorem solution (a b M : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hM : 0 ≤ M)
    (he : 0 ≤ M^2-a-b) (hc : 4*a*b ≤ (M^2-a-b)^2) :
    Real.sqrt a + Real.sqrt b ≤ M := by
  have hp : (2*Real.sqrt a*Real.sqrt b)^2 = 4*a*b := by
    simp only [mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb]
    ring
  have hn : 0 ≤ 2*Real.sqrt a*Real.sqrt b := by positivity
  have ht : 2*Real.sqrt a*Real.sqrt b ≤ M^2-a-b := by
    nlinarith only [he, hc, hp, hn]
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  have hna := Real.sqrt_nonneg a
  have hnb := Real.sqrt_nonneg b
  nlinarith
