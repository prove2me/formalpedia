-- Prove2me | solution 1 for OnlineCRS.Matching.exponential_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-18T19:33:39.244488+00:00
-- url     : https://prove2.me/submissions/a87edb55-2694-4947-8e70-49602aef7384

import Mathlib

set_option autoImplicit false

theorem solution (t : ℝ) (ht : 0 < t) :
    1 ≤ Real.exp t * (Real.exp t - 1) / t := by
  rw [le_div_iff₀ ht]
  have h1 : t + 1 ≤ Real.exp t := Real.add_one_le_exp t
  have h2 : 1 ≤ Real.exp t := by linarith
  nlinarith
