-- Prove2me | solution 1 for ProximityPrize.SubmissionUpper.PrescribedTop.four_mul_le_sq
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-09-27T18:05:01.140465+00:00
-- url     : https://prove2.me/submissions/7daf2af5-8ab6-4293-81df-d7927b6d6ac3

import Mathlib
import Init
/-!
# A prescribed-top-coefficient collision family below half radius

The included baseline attacks at radius `1/2` using the word `X^m` together with
*every* `m`-subset of the domain as an interpolation set.  This file generalises
that construction: it uses `t`-subsets with `t = m + r`, restricted to those whose
vanishing polynomial shares its top `r` coefficients with a fixed one.  Each such
subset still yields a genuine codeword agreeing with a single fixed word on all `t`
points, so the attack survives at radius `(n - t)/n = 1/2 - r/n`.

With `r = 8431` this certifies the unsafe suffix from grid index `122641` onward.
-/

namespace ProximityPrize.SubmissionUpper.PrescribedTop

open Polynomial
                                   
                             
open scoped NNReal


                             














































/-- `4ab <= (a+b)^2`. -/
theorem _root_.solution (a b : ℕ) : 4 * (a * b) ≤ (a + b) ^ 2 := (by
  have h : 2 * a * b ≤ a ^ 2 + b ^ 2 := two_mul_le_add_sq a b
  nlinarith [h]
)
end PrescribedTop
end SubmissionUpper
end ProximityPrize
