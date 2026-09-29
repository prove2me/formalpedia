-- Prove2me | solution 1 for ProximityPrize.SubmissionUpper.PrescribedTop.numeric_fact2
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-09-27T06:01:32.238541+00:00
-- url     : https://prove2.me/submissions/7c662cc7-304b-40a0-9b9e-4cbfcfd5c8bc

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


                             

































































set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000000 in
set_option exponentiation.threshold 900000 in
theorem _root_.solution :
    131072 ^ 2 * (((2 ^ 31 - 2 ^ 24 + 1) ^ 8431 * 2 ^ 59) ^ 2) * 270576 ^ 16862
      ≤ 4 ^ 8431 * (4 ^ 131072) ^ 2 * ((131072 : ℕ) * 122642) ^ 8431 := (by decide
)
end PrescribedTop
end SubmissionUpper
end ProximityPrize
